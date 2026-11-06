import VersoManual
open Verso.Genre Manual
#doc (Manual) "第4章 Full strong exceptional collection" =>

# 定義と命題

三角圏の対象 $`E` が exceptional とは $`\operatorname{Hom}(E,E[q])=0`（$`q\neq0`）かつ $`\operatorname{End}(E)=k` となること。
列 $`(E_0,\ldots,E_n)` が exceptional とは各項が exceptional で、$`j>i` なら $`\operatorname{Hom}(E_j,E_i[q])=0` が全ての $`q` で成立すること。
さらに任意の二項間の高次 Hom が消えれば strong、thick に生成すれば full という。

**定理。** $`(\mathcal O,\mathcal O(1),\ldots,\mathcal O(n))` は full strong exceptional collection である。

**証明。** $`\operatorname{End}(\mathcal O(i))=H^0(X,\mathcal O)=k` である。
第2章から、任意の $`i,j` について $`q\neq0` の Ext が消え、$`i>j` の Hom も消える。
従って strong exceptional である。
第3章の対角線分解による thick 生成性から full である。証明終。

# Tilting bundle

**系。** $`T=\bigoplus_{i=0}^n\mathcal O(i)` は、非零次数の自己 Ext を持たず $`D^b(\operatorname{Coh}X)` を thick に生成する tilting bundle である。

**証明。** 有限直和に対する Ext の加法性と前定理による。証明終。
