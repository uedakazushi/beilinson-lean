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

# Semiorthogonal decomposition による fullness

**定理。** $`(\mathcal O,\mathcal O(1),\ldots,\mathcal O(n))` は full exceptional collection である。

**証明。** 第2章の Ext 計算により、これらは exceptional collection である。
$`X` は滑らかで射影的なので $`\mathcal D` は $`k` 上 Hom-finite かつ Serre functor を持つ。
例外対象の生成する部分圏は admissible であり、例外対象の列から半直交分解が得られる。
特に $`\mathcal A` の右直交を用いる形の semiorthogonal decomposition が存在する
（成分の並べ方は semiorthogonal decomposition の規約に依存する）。
前系により右直交成分は零だから $`\mathcal A=\mathcal D`。証明終。

ここで **admissibility** は右直交が零であることから生成性へ進むための必要な論理的橋渡しである。
Serre functor や admissibility を仮定せず、単に $`\mathcal A^\perp=0` だから $`\mathcal A=\mathcal D` と結論することはしない。
