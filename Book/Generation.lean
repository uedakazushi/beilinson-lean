import VersoManual
open Verso.Genre Manual
#doc (Manual) "第3章 線束の生成性と直交圏" =>

# 線束の Koszul 完全列

$`X=\mathbb P(V)` において、$`W=V^\vee=H^0(X,\mathcal O(1))` とおく。
自然な評価射
$$`W\otimes_k\mathcal O_X(-1)\longrightarrow\mathcal O_X`
は、斉次座標のいずれかが各点で非零となるので全射である。
その核を含む Koszul 複体は次の完全列を与える：

$$`0\longrightarrow\bigwedge^{n+1}W\otimes\mathcal O(-n-1)\longrightarrow\bigwedge^nW\otimes\mathcal O(-n)\longrightarrow\cdots\longrightarrow W\otimes\mathcal O(-1)\longrightarrow\mathcal O\longrightarrow0.`

**証明。** 射影空間の各標準開集合 $`D_+(x_i)` では、評価射の成分の一つが可逆である。
このとき Koszul 複体は収縮ホモトピーを持つので完全である。
これらの標準開集合が $`X` を被覆するから、複体は全体で完全である。証明終。

この Koszul 完全列は **射影空間上の基点を持たない線形形式の列** に対するものであり、
$`X\times X` の対角線の分解は使わない。

# 任意の負の捻りを構成する

$`\mathcal D=D^b(\operatorname{Coh}X)` とし、
$$`\mathcal A=\operatorname{thick}\langle\mathcal O,\mathcal O(1),\ldots,\mathcal O(n)\rangle\subseteq\mathcal D`
とおく。

**補題。** 任意の整数 $`k\geq0` について $`\mathcal O(-k)\in\mathcal A` である。

**証明。** $`n=0` なら $`X=\operatorname{Spec}k` であり、全ての $`\mathcal O(-k)` は
$`\mathcal O` と同型なので明らか。
以下 $`n\geq1` とする。$`k=0` の場合は定義から成立する。

$`m\geq0` とし、$`\mathcal O(-m),\mathcal O(-m+1),\ldots,\mathcal O(n)` が
$`\mathcal A` に属すると仮定する。
上の Koszul 完全列を $`\mathcal O(n-m)` で捻ると

$$`0\longrightarrow\bigwedge^{n+1}W\otimes\mathcal O(-m-1)\longrightarrow\bigwedge^nW\otimes\mathcal O(-m)\longrightarrow\cdots\longrightarrow W\otimes\mathcal O(n-m-1)\longrightarrow\mathcal O(n-m)\longrightarrow0.`

先頭以外の項の捻り次数は $`-m,-m+1,\ldots,n-m` に含まれ、
$`n-m\leq n` だから帰納法の仮定で全て $`\mathcal A` に属する。
有限完全列は導来圏で有限回の cone により構成できるため、先頭項も $`\mathcal A` に属する。
$`\bigwedge^{n+1}W` は一次元の $`k`-ベクトル空間なので、
$`\mathcal O(-m-1)\in\mathcal A` となる。帰納法が完了する。証明終。

# Right orthogonal と Serre の定理

$`\mathcal A^\perp` は、
$`F\in\mathcal D` であって全ての $`E\in\mathcal A`、$`q\in\mathbb Z` に対し
$`\operatorname{Hom}_{\mathcal D}(E,F[q])=0` を満たす対象のなす充満部分圏である。

**補題（負捻り線束による検出）。** $`F\in D^b(\operatorname{Coh}X)` が
$$`\operatorname{Hom}_{\mathcal D}(\mathcal O(-k),F[q])=0\quad(k\geq0,\ q\in\mathbb Z)`
を満たすなら $`F=0` である。

**証明。** $`F\neq0` と仮定し、ある $`q` で $`\mathcal H^q(F)\neq0` とする。
Serre の定理により、十分大きい $`k` に対して各 $`\mathcal H^j(F)(k)` は高次コホモロジーを持たず、
かつ $`\mathcal H^q(F)(k)` は大域切断で生成される。
後者は非零の連接層なので $`H^0(X,\mathcal H^q(F)(k))\neq0`。
$`F` は有界なので、さらに同じ $`k` で全ての非零コホモロジー層について高次コホモロジーの消滅を選べる。
hypercohomology spectral sequence

$$`E_2^{p,j}=H^p(X,\mathcal H^j(F)(k))\Longrightarrow\mathbb H^{p+j}(X,F(k))`

は $`p=0` の列へ退化する。ゆえに
$$`\mathbb H^q(X,F(k))\cong H^0(X,\mathcal H^q(F)(k))\neq0.`
ところが $`\mathcal O(-k)` は局所自由であるから
$$`\operatorname{Hom}_{\mathcal D}(\mathcal O(-k),F[q])\cong\mathbb H^q(X,F(k)),`
となり仮定に矛盾する。従って $`F=0`。証明終。

**系。** $`\mathcal A^\perp=0`。

**証明。** 上の負捻り線束が全て $`\mathcal A` に属するので、右直交対象は前補題の仮定を満たす。証明終。

# 有限 total Hom と評価射

右直交の消滅を fullness へ結びつけるため、必要な admissibility を具体的に構成する。
三角圏 $`\mathcal D` の二対象について「total Hom が有限」とは、
各 $`\operatorname{Hom}(E,F[q])` が有限次元であり、かつ非零となる整数 $`q` が有限個しかないことをいう。
各次数の有限次元性だけでは、以下の評価射の始域が有限直和になるとは限らない。

**補題（例外対象による射影）。** $`E` を $`k`-線形三角圏の例外対象とし、
$`E` から $`F` への total Hom が有限であるとする。このとき三角
$$`U_E(F)\longrightarrow F\longrightarrow Q_E(F)\longrightarrow U_E(F)[1]`
が存在し、$`U_E(F)\in\operatorname{thick}\langle E\rangle`、
$`\operatorname{Hom}(E,Q_E(F)[r])=0`（全ての $`r`）を満たす。

**証明。** 各 $`q` について $`\operatorname{Hom}(E,F[q])` の基底を選ぶ。
各基底ベクトルを $`E[-q]\to F` と読み、これらを成分に持つ評価射を作る：
$$`U_E(F)=\bigoplus_{q\in\mathbb Z}\operatorname{Hom}(E,F[q])\otimes_k E[-q]\longrightarrow F.`
ここで有限次元ベクトル空間と対象の tensor は、基底を選んだ有限直和を意味する。
仮定から直和全体も有限である。$`Q_E(F)` をこの射の cone とする。
例外性から $`\operatorname{Hom}(E,E[t])` は $`t=0` 以外では零であり、$`t=0` では $`k`。
従って各 $`r` に対し評価射が誘導する
$$`\operatorname{Hom}(E,U_E(F)[r])\longrightarrow\operatorname{Hom}(E,F[r])`
は、選んだ基底を送る同型となる。三角の Hom 長完全列から、cone への全ての次数の Hom は零である。証明終。

# Semiorthogonal decomposition による fullness

**補題（有限例外列の充満性判定）。** $`(E_0,\ldots,E_n)` を例外列とし、
各 $`E_i` から全ての対象への total Hom が有限であるとする。
この列の右直交が零なら、$`\operatorname{thick}\langle E_0,\ldots,E_n\rangle=\mathcal D`。

**証明。** 任意の $`F` から始め、前補題で $`E_n,E_{n-1},\ldots,E_0` の順に Hom を消す。
既に $`E_j` からの全シフト Hom が零である対象に対し、$`i<j` の段階で取り除く項は
$`E_i` の有限直和とシフトからなる。半直交性
$`\operatorname{Hom}(E_j,E_i[q])=0` により、この項への Hom も零であるから、
新しい cone でも $`E_j` からの消滅は保たれる。
最後の対象は全ての $`E_i` の右直交に属するので零。
各段階の三角を逆順にたどると、取り除いた有限直和・シフトと有限回の cone から
元の $`F` が構成される。従って $`F` は生成部分圏に属する。証明終。

これは例外列の右射影と半直交分解を与える具体的な議論である。
右直交が零であるという条件だけから fullness を結論したのではなく、
有限 total Hom による有限の評価射を構成したことが論理的な橋渡しとなっている。

**定理。** $`(\mathcal O,\mathcal O(1),\ldots,\mathcal O(n))` は full exceptional collection である。

**証明。** 第2章のコホモロジー計算により例外列である。
$`F\in D^b(\operatorname{Coh}X)` に対し、
$$`\operatorname{Hom}(\mathcal O(i),F[q])=\mathbb H^q(X,F(-i)).`
連接層のコホモロジーは射影性により有限次元で、次数 $`0,\ldots,n` の外で零。
$`F` のコホモロジー層は有限個なので、hypercohomology spectral sequence により
上の Hom も各次数で有限次元、かつ有限個の次数以外で零である。
従って有限 total Hom の仮定が満たされる。
前節の Koszul 帰納法と Serre の定理により右直交は零だから、前補題を適用できる。証明終。
