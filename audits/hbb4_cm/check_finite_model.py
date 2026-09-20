"""Finite CM investigation; executable semantic check, not a Lean proof.

World (p, i) has the first i events as its causal past. Events themselves
carry that prefix. Event atoms additionally require actual event membership.
All participants are live; both learners have all size >= 2 quorums.
Correlation is total and constant, so MaxDepth is exactly 1.
"""
from itertools import combinations, product

PARTICIPANTS = range(3)
LEARNERS = ('a', 'b')
VALUES = ('a', 'b', '0', '1')
ALL = frozenset(PARTICIPANTS)
QUORUMS = tuple(frozenset(q) for n in (2, 3)
                for q in combinations(PARTICIPANTS, n))
DEPTH = 1
CAP = DEPTH + 1


def execution():
    events = [(0, ('propose', '0'))]
    events += [(p, ('echo', '0')) for p in PARTICIPANTS]
    # Direct certificates must exist before cross-source transfers.
    for n in range(CAP + 1):
        events += [(p, ('vote', l, l, '0', n))
                   for l, p in product(LEARNERS, PARTICIPANTS)]
    for n in range(CAP + 1):
        events += [(p, ('vote', l, s, '0', n))
                   for l, s, p in product(LEARNERS, LEARNERS, PARTICIPANTS)
                   if l != s]
    events += [(p, ('deliver', l, '0'))
               for l, p in product(LEARNERS, PARTICIPANTS)]
    # First sweep observes every performed atom; second observes every
    # K E / Q_l E witness needed by restricted Knowledge.
    events += [(p, None) for _ in range(2) for p in PARTICIPANTS]
    return events


def check(events, cap=CAP):
    end = len(events)

    def past(i, p, body):
        return any(q == p and body(j) for j, (q, _) in enumerate(events[:i]))

    def known(i, atom):
        return any(e == atom for _, e in events[:i])

    def quorum(i, body):
        return any(all(past(i, p, body) for p in q) for q in QUORUMS)

    def cert(i, l, v, n, source=None):
        return quorum(i, lambda j: events[j][1] is not None
                      and events[j][1][0] == 'vote'
                      and events[j][1][1] == l
                      and (source is None or events[j][1][2] == source)
                      and events[j][1][3:] == (v, n))

    def echo_cert(i, v):
        return quorum(i, lambda j: events[j][1] == ('echo', v))

    def legal(i, v):
        votes = [e for _, e in events[:i] if e and e[0] == 'vote']
        return all(any(f[3] == v and f[4] > e[4] for f in votes)
                   for e in votes if e[3] != v)

    def sometime(p, atom):
        return (p, atom) in events

    # Backward and event-local rules: outside actual events the event
    # antecedents are false, including counterfactual event labels.
    for i, (p, e) in enumerate(events):
        if e is None:
            continue
        if e[0] == 'echo':
            assert known(i, ('propose', e[1])), ('Echo?', i)
            assert all(f[1] == e[1] for q, f in events[:i]
                       if q == p and f and f[0] == 'echo'), ('EchoNE', i)
        elif e[0] == 'vote':
            _, l, s, v, n = e
            assert 0 <= n <= cap, ('round bound', i)
            assert legal(i, v), ('VoteNE', i)
            if n == 0:
                assert (l == s and echo_cert(i, v)) or cert(i, s, v, DEPTH), ('Vote0?', i)
            else:
                assert cert(i, l, v, n - 1, s), ('VoteN?', i)
        elif e[0] == 'deliver':
            assert cert(i, e[1], e[2], DEPTH + 1), ('Deliver?', i)

    # Every prefix and participant, not just the scheduled event's world.
    for i, p in product(range(end + 1), PARTICIPANTS):
        for v in VALUES:
            if known(i, ('propose', v)):
                assert any(sometime(p, ('echo', u)) for u in VALUES), ('Echo!', i, p)
            for l in LEARNERS:
                if legal(end, v) and echo_cert(i, v):
                    assert sometime(p, ('vote', l, l, v, 0)), ('Vote0E!', i, p)
                for s in LEARNERS:
                    if legal(end, v) and cert(i, s, v, DEPTH):
                        assert sometime(p, ('vote', l, s, v, 0)), ('Vote0V!', i, p)
                    for n in range(1, cap + 1):
                        if legal(end, v) and cert(i, l, v, n - 1, s):
                            assert sometime(p, ('vote', l, s, v, n)), ('VoteN!', i, p, n)
                if cert(i, l, v, DEPTH + 1):
                    assert sometime(p, ('deliver', l, v)), ('Deliver!', i, p)

    # All finite outer learner lists, via the exact finite closure of their
    # intersection families. Both learners interpret the same semifilter.
    families = []
    family = frozenset((ALL,))
    while family not in families:
        families.append(family)
        family = frozenset(a & q for a in family for q in QUORUMS)
    atoms = {e for _, e in events if e is not None}
    # Any unperformed event atom (including all higher ranks) is false at
    # every event, hence has exactly this representative's semantics.
    atoms.add(('unperformed',))
    bodies = []
    for atom in atoms:
        bodies.append(lambda j, a=atom: events[j][1] == a)
        bodies.append(lambda j, a=atom: known(j, a))
        for _ in LEARNERS:
            bodies.append(lambda j, a=atom: quorum(j, lambda k: events[k][1] == a))
    for body, family in product(bodies, families):
        def diamond(i):
            good = {p for p in PARTICIPANTS if past(i, p, body)}
            return all(bool(q & good) for q in family)

        def box(i):
            good = {p for p in PARTICIPANTS if past(i, p, body)}
            return any(q <= good for q in family)

        for modality in (diamond, box):
            if modality(end):
                for p in PARTICIPANTS:
                    assert any(q == p and modality(j) for j, (q, _) in enumerate(events)), (
                        'Knowledge', p, family)

    # LiveAlways and CM: interpretations are constant. LiveSeq and Rseq:
    # prefix histories totally order all events; every pair of quorums meets.
    assert all(q & r for q, r in product(QUORUMS, repeat=2))
    assert any(not (q & r & s) for q, r, s in product(QUORUMS, repeat=3))
    # Both liveness antecedents have witnesses, including a != b transfer.
    assert {e[1] for _, e in events if e and e[0] == 'propose'} == {'0'}
    assert any(known(j, ('propose', '0')) for j in range(end))
    assert sometime(0, ('deliver', 'a', '0'))
    assert all(sometime(p, ('deliver', l, '0'))
               for p, l in product(PARTICIPANTS, LEARNERS))
    return len(families), len(bodies)


def main():
    events = execution()
    families, bodies = check(events)
    print(f'PASS: {len(events)} events; {3 * (len(events) + 1)} participant/prefix worlds; '
          f'{bodies} Knowledge bodies; {families} outer-list equivalence classes.')
    # A necessary next-round obligation is visible as soon as the cap moves.
    try:
        check(events, cap=CAP + 1)
    except AssertionError as error:
        assert error.args[0][0] == 'VoteN!', error
        print(f'EXPECTED FAILURE without stopping at delivery rank: {error}')
    else:
        raise AssertionError('Missing detection of the next-round obligation')
    # Actual protocol events alone do not guarantee the restricted Knowledge
    # obligations: observing terminal deliveries still requires later events.
    try:
        check(events[:-6])
    except AssertionError as error:
        assert error.args[0][0] == 'Knowledge', error
        print('EXPECTED FAILURE for protocol events without observation sweeps.')
    else:
        raise AssertionError('Missing detection of terminal Knowledge obligations')


if __name__ == '__main__':
    main()
