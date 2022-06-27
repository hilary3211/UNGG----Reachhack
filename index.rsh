'reach 0.1'

const player_common = {
    ...hasRandom,
    seeWinner: Fun([UInt], Null),
    informTimeout: Fun([], Null)
}

export const main = Reach.App(() => {
    const NumGenAi = Participant('NumGenAi', {
        ...player_common,
        deadline: UInt,
        getunique_numset: Tuple(UInt, UInt, UInt, UInt, UInt)//Array(UInt, 5)
    })
    const Player1 = Participant('Player1', {
        ...player_common,
        wager: UInt,
        getnum: Fun([], UInt)
    })
    const Player2 = Participant('Player2', {
        ...player_common,
        acceptwager: Fun([UInt], Null),
        getnum: Fun([], UInt)
    })

    init();

    const informTimeout = () => {
        each([NumGenAi, Player1, Player2], () => {
            interact.informTimeout();
        })
    }

    NumGenAi.only(() => {
        const _getnumset = interact.getunique_numset
        const [_commitgetnumset, _saltgetnumset] = makeCommitment(interact, _getnumset)
        const commitgns = declassify(_commitgetnumset)
        const deadline = declassify(interact.deadline)
    })
    NumGenAi.publish(commitgns, deadline);
    commit()
    unknowable(Player1, NumGenAi(_getnumset, _saltgetnumset))
    unknowable(Player2, NumGenAi(_getnumset, _saltgetnumset))
    Player1.only(() => {
        const wager = declassify(interact.wager)
    })
    Player1.publish(wager)
        .pay(wager)
    commit()

    Player2.only(() => {
        const acceptwager = declassify(interact.acceptwager(wager))
    });
    Player2.publish(acceptwager)
        .pay(wager)

    var i = 0
    invariant(balance() == (2 * wager));
    while (i < 3) {
        commit();

        Player1.only(() => {
            const _getnum = interact.getnum();
            const [_commitgetnum, _saltgetnum] = makeCommitment(interact, _getnum)
            const commitgetnum = declassify(_commitgetnum)
        });

        Player1.publish(commitgetnum)
        commit();
        unknowable(Player2, Player1(_getnum, _saltgetnum))
        unknowable(NumGenAi, Player1(_getnum, _saltgetnum))

        Player2.only(() => {
            const player2num = declassify(interact.getnum());
        })
        Player2.publish(player2num)
        commit();

        Player1.only(() => {
            const saltplayer1 = declassify(_saltgetnum)
            const player1num = declassify(_getnum)
        })
        Player1.publish(saltplayer1, player1num);
        checkCommitment(commitgetnum, saltplayer1, player1num)
        commit()
        NumGenAi.only(() => {
            const saltnumAi = declassify(_saltgetnumset)
            const numset = declassify(_getnumset)
        })
        NumGenAi.publish(saltnumAi, numset)
        checkCommitment(commitgns, saltnumAi, numset)
        const [num1, num2, num3, num4, num5] = numset

        if (num1 == player1num && num1 != player2num || num2 == player1num && num2 != player2num || num3 == player1num && num3 != player2num || num4 == player1num && num4 != player2num || num5 == player1num && num5 != player2num) { //|| num2 == player1num || num3 == player1num || num4 == player1num || num5 == player1num && num1 != player2num || num2 != player2num || num3 != player2num || num4 != player2num || num5 != player2num) {
            i = 10
            continue;
        } else {
            if (num1 == player2num && num1 != player1num || num2 == player2num && num2 != player1num || num3 == player2num && num3 != player1num || num4 == player2num && num4 != player1num || num5 == player2num && num5 != player1num) { //|| num2 == player2num || num3 == player2num || num4 == player2num || num5 == player2num && num1 != player1num || num2 != player1num || num3 != player1num || num4 != player1num || num5 != player1num) {
                i = 11
                continue;
            } else {
                if (num1 == player2num && num1 == player1num || num2 == player2num && num2 == player1num || num3 == player2num && num3 == player1num || num4 == player2num && num4 == player1num || num5 == player2num && num5 == player1num) {
                    i = 12
                    continue
                }
            }
            i = i + 1
            continue

        }
    }
    if (i == 10) {
        transfer(2 * wager).to(Player1)
    } else {
        if (i == 11) {
            transfer(2 * wager).to(Player2)
        } else {
            if (i == 12) {
                transfer(wager).to(Player1)
                transfer(wager).to(Player2)
            } else {
                transfer(wager).to(Player1)
                transfer(wager).to(Player2)
            }
        }
    }
    commit();


})