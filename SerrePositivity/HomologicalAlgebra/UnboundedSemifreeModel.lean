module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBaseChange
public import SerrePositivity.DifferentialGraded.Tensor.Graded

/-!
# 非有界な底変換の半自由模型

## 概要
任意の通常の複体の半自由分解と、底変換前後の K-flat 性を供給する。

## 方針
既存の一点 dg 環上の半自由分解と、次数ごとの基底の底変換を再利用する。

## 規約
型に現れるのは通常の鎖複体と環射だけ。BS 著者版 Construction 6.1 の模型の入力。

## 使われ方
正則列の商と結晶被覆の導来テンソルを非有界な入力で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory DifferentialGraded InfinityCategories

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：通常の半自由複体は K-flat。
方針：一点 dg 環の Hom の K-flat 性と既存の objectwise 判定を使う。
規約：非有界、BS 著者版 Construction 6.1 の計算模型。
使われ方：Koszul の増大をテンソルに通す。 -/
theorem semifreeComplex_isKFlat {P : Complex R} (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R P) :
    complexKFlat R P :=
  moduleSemifree_objectwiseKFlat R PUnit.{1} (fun _ _ => complexKFlat_unit R) hP PUnit.unit

/-- 概要：半自由な分解上の任意の底変換も K-flat。
方針：既存の基底の底変換による半自由性の保存を使う。
規約：平坦性を要求しない、BS 著者版 Construction 6.1。
使われ方：結晶被覆上での p の Koszul 分解の比較。 -/
theorem semifreeComplex_baseChange_isKFlat (f : R →+* S)
    {P : Complex R} (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R P) :
    complexKFlat S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj P) :=
  semifreeComplex_isKFlat (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_baseChange f hP)

/-- 概要：任意の非有界複体に、底変換の前後で K-flat な実際の分解がある。
方針：既存の次数ごと全射な半自由分解を取り、二つの K-flat 判定を付ける。
規約：BS 著者版 Construction 6.1。存在しない模型の仮定を置かない。
使われ方：任意の入力の導来テンソルを分解上で評価する。 -/
theorem exists_unbounded_baseChange_model (f : R →+* S) (K : Complex R) :
    ∃ (P : Complex R) (q : P ⟶ K), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R P ∧ QuasiIso q ∧
      (∀ i : ℤ, Function.Surjective (q.f i)) ∧ complexKFlat R P ∧
        complexKFlat S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f).obj P) := by
  obtain ⟨P, q, hP, hq, hW⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_complexSemifree_resolution R K
  exact ⟨P, q, hP, hW, hq, semifreeComplex_isKFlat hP, semifreeComplex_baseChange_isKFlat f hP⟩

end SerrePositivity
