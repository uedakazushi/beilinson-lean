import VersoManual
open Verso.Genre Manual
#doc (Manual) "第1章 主定理と規約" =>

# 主定理

体 $`k`、次元 $`n+1` の $`k`-ベクトル空間 $`V` を取り、射影空間 $`X=\mathbb P(V)` は $`V` の一次元部分空間を分類するものとする。
$`n\geq0`。$`\mathcal O_X(-1)` を tautological line bundle、$`\mathcal O_X(1)` をその双対とする。

$$`T=\bigoplus_{i=0}^{n}\mathcal O_X(i),\qquad A_n=\operatorname{End}_X(T).`

**Beilinson の定理。** 有限次元右 $`A_n`-加群の圏を $`\operatorname{mod}_{\mathrm{fd}}A_n` と書くと、
$$`\mathbf R\operatorname{Hom}_X(T,-): D^b(\operatorname{Coh}X)\xrightarrow{\sim}D^b(\operatorname{mod}_{\mathrm{fd}}A_n)`
は三角圏同値である。また $`A_n` は関係式付き Beilinson 箙の経路代数である。

右加群規約を使うのは、$`\operatorname{Hom}_X(T,F)` への $`\operatorname{End}_X(T)` の前合成作用が右作用だからである。

# 全体の証明計画

線束コホモロジーから $`\operatorname{Ext}^{>0}(T,T)=0` を証明する。
線束の Koszul 完全列によって全ての $`\mathcal O(-k)` を作り、Serre の定理から right orthogonal が零であることを示す。有限 total Hom から評価射の cone によって例外列の右射影を構成し、$`T` の thick 生成性を得る。
この二つを抽象的な tilting theorem に代入し、終域の代数を Hom の掛け算から同定する。

必要な基礎は層・射影空間・局所自由分解・Koszul 複体・導来圏である。
後から形式化する際のため、幾何学的な生成性と導来 Hom–tensor 随伴の部分を分離する。
