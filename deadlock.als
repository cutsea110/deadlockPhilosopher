open util/ordering[State]

-- 哲学者
sig Philosopher {
	-- 左と右には異なる１本のフォークがある
	disj leftFork, rightFork: one Fork,
	-- 左と右には異なる哲学者が１人ずついる
	left, right: one Philosopher
}
-- フォーク
sig Fork { 
	-- フォークの左と右には異なる哲学者が一人ずついる
	disj left, right: one Philosopher
}
fact{
	-- フォークと哲学者の数は同じ
	#Philosopher = #Fork
	-- すべての哲学者に対して、右(左)の哲学者は、右(左)のフォークの右(左)の哲学者と等しい
	(all p: Philosopher | p.left = p.leftFork.left and p.right = p.rightFork.right )
	-- すべてのフォークに対して、左(右)の哲学者の右(左)のフォークは自分
	(all f: Fork | f = f.left.rightFork and f = f.right.leftFork)
}
-- テーブルは一つ
fact OneTable{
	-- すべての哲学者に対して、どの哲学者も左、左(右、右)とたどる事で到達できる
	-- left(right)の推移的閉包は哲学者全体を含む
	(all p: Philosopher | Philosopher in p.^right and Philosopher in p.^left)
	-- すべてのフォークに対して、どのフォークも左、左(右、右)とたどる事で到達できる
	-- left.leftFork(right.rightFork)の推移的閉包はフォーク全体を含む
	(all f: Fork | Fork in f.^( left.leftFork ) and Fork in f.^( right.rightFork ))
}

-- Global State
sig State {
        -- フォークの保持者は高々一人(lone:least or equal to one)
	owned: Fork -> lone Philosopher
}{
	-- フォークは自分の両脇の哲学者からしか保持されない
	-- f.ownedでも良いが、ボックス結合を使って読みやすく(a.bをb[a]って書ける)
	all f:Fork | owned[f] in f.(left+right)
}
-- フォークの為の述語
-- ある状態sでフォークfはフリーである（誰にも保持されていない）
pred free ( s: State, f: Fork ) {
	no s.owned [ f ]
}

-- 哲学者の為の述語
-- ある状態sで哲学者pは食べている（両隣のフォークの保持者がpである）
pred eating ( s: State, p: Philosopher ) {
	p  = s.owned[p.rightFork] and p =  s.owned[p.leftFork]
}

-- アルゴリズム
-- 状態sで哲学者pが左のフォークを取った状態がs'である
pred TakeLeft ( s: State, s': State, p: Philosopher ) {
	-- sではpの左のフォークは空いていて、s'ではpの左のフォークはpが保持している
	-- (述語に引数を適用する場合には[]を使う)
	free[s,p.leftFork] and s'.owned[p.leftFork] = p
	-- それ以外のフォークは保持者が変化していない
	and (all f: (Fork - p.leftFork) | s.owned[f] = s'.owned[f])
}
-- 状態sで哲学者pが右のフォークを取った状態がs'である
pred TakeRight ( s: State, s': State, p: Philosopher ) {
	free[s,p.rightFork] and s'.owned[p.rightFork] = p
	and (all f: (Fork - p.rightFork) | s.owned[f] = s'.owned[f])
}
-- 状態sで哲学者pが食べていて、両方のフォークを手放した状態がs'である。
pred Release(s:State, s':State, p:Philosopher){
	eating[s,p] and (free[s',p.rightFork] and free[s',p.leftFork])	
	and (all f: (Fork - (p.leftFork + p.rightFork)) | s.owned[f] = s'.owned[f])
}

-- 初期状態の述語
pred init ( s: State ) {
	all f: Fork | free [ s, f ]
}
-- 状態上の全順序に与える制約
fact Traces {
	-- firstはinitを満たす
	init [ first ] 
	-- 最後の状態以外の状態sは
	-- 誰かが動作できる状態ならsの次の状態next[s]は誰かが動いた後の状態であり、
	-- かつ、そう出なければ、何も変わっていない(デッドロックが続いている)
	all s: State - last
		| SomeoneCanMove[s] => SomeoneActioned[s,next[s]] else s.owned = next[s].owned
} 
-- 状態sで、誰かが動いた状態がs'である。
pred SomeoneActioned ( s: State, s': State ) {
	some p: Philosopher | TakeLeft [ s, s', p ] or TakeRight [ s, s', p ] or Release[s,s',p] 
}
-- 状態sで誰かが動作できる。
pred SomeoneCanMove(s:State){
	some p: Philosopher | 
		free[s,p.leftFork] or free[s,p.rightFork] or eating[s,p]
}

-- デッドロックが存在する実行である
pred WithDeadLock{
	-- ある状態sは、初めてのデッドロック状態で、その後ずっとデッドロック。
	some s:State | not SomeoneCanMove[s] 
				and all s': s.^next | not SomeoneCanMove[s'] -- s以降のs'はずっとデッドロック
				and all s'': s.^prev | SomeoneCanMove[s''] -- s以前はずっと誰かが動ける
}
-- デッドロックが存在する実行を見つけてくれ、というコマンド。
-- 3フォーク、3人の哲学者、実行の長さは10ステップ
run WithDeadLock for exactly 3 Fork, 3 Philosopher,  10 State
