module
public import SerrePositivity.KST.SConstruction.CofiberFamilies
public import SerrePositivity.KST.SConstruction.ArCofiberFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimits
public import SerrePositivity.KST.SConstruction.FunctorInitialVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-! # cofiber の族を関手圏の cofiber 列にする
概要：パラメーター付きの普遍四角形は関手 ∞ 圏で普遍四角形となる。
方針：内部 Hom の転置と点ごとの零対象・押し出しの判定を用いる。
規約：族を供給すれば安定性は追加仮定しない。
使われ方：Ar[n] 上の cofiber 補完から gapped 条件への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：転置した関手の指定点での評価は元の族のその関手。
方針：二回の転置の逆律と零次成分の公式を使う。
規約：任意の単体集合で成立。使われ方：cofiber の族の各点の四角形。 -/
lemma internalHomFlipHomEquiv_evaluate {A B X : SSet.{u}}
    (H : A ⟶ (ihom B).obj X) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B X H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B X).symm (H.app (Opposite.op ⦋0⦌) a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B X H) a
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B A X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B X H) = H :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B X).symm_apply_apply H
  rw [he] at h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [← h]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B X).apply_symm_apply _).symm

/-- 概要：cofiber 図式の零角は内部 Hom の角での評価でも零対象。
方針：関手頂点を実際の四角形で表示して評価する。
規約：C に仮定はない。使われ方：関手圏の零角の点ごとの判定。 -/
lemma IsCofiberDiagramVertex.zero_evaluation {C : SSet.{u}}
    {v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌}
    (hv : IsCofiberDiagramVertex v) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) v) := by
  have hvF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) = v :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply v
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v)
  rw [hvF] at he
  rw [he]
  exact hv.1

/-- 概要：cofiber の族を関手圏の一つの四角形に転置する。
方針：内部 Hom の始域を交換する。
規約：高次パラメーターを保持する。使われ方：点ごとの普遍性の関手圏への移送。 -/
def cofiberFamilySquare {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom A).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A (Δ[1] ⊗ Δ[1] : SSet.{u}) C
    (H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)

/-- 概要：関手圏の四角形の各点での評価は元の cofiber 四角形。
方針：転置の評価式を適用する。
規約：厳密等号。使われ方：点ごとの押し出し性。 -/
lemma cofiberFamilySquare_evaluate {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) (a : A _⦋0⦌) :
    cofiberFamilySquare H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).symm
        (H.app (Opposite.op ⦋0⦌) a).val :=
  internalHomFlipHomEquiv_evaluate _ a

/-- 概要：cofiber の族の左上角は関手圏でも零対象。
方針：内部 Hom の転置の零次成分と点ごとの零対象判定を使う。
規約：C の quasicategory 性は不要。使われ方：関手圏の ZeroTriangle の零角。 -/
lemma cofiberFamilySquare_zero_corner {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (cofiberFamilySquare H) 0 1) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((cofiberFamilySquare H).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  rw [cofiberFamilySquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  apply isZeroVertex_functorVertex_of_pointwise
  intro a
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (H.app (Opposite.op ⦋0⦌) a)).zero_evaluation

/-- 概要：cofiber の族は関手圏で零角を持つ四角形。
方針：転置した四角形と零角の普遍性をまとめる。
規約：安定性は定義に不要。使われ方：cofiber 列の点ごとの構成。 -/
def cofiberFamilyTriangle {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle ((ihom A).obj C) :=
  ⟨cofiberFamilySquare H, cofiberFamilySquare_zero_corner H⟩

/-- 概要：cofiber 四角形の族は関手 ∞ 圏の cofiber 列。
方針：各頂点での押し出し性を関手圏の点ごとの余極限判定へ渡す。
規約：C は quasicategory。A は任意で安定性の追加仮定は不要。
使われ方：Ar[n] 全体の cofiber 補完と押し出しの貼り合わせ。 -/
lemma cofiberFamilyTriangle_isCofiber {A C : SSet.{u}} [Quasicategory C]
    (H : A ⟶ cofiberDiagrams C) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (cofiberFamilyTriangle H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise (cofiberFamilySquare H)
  intro a
  rw [cofiberFamilySquare_evaluate]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (H.app (Opposite.op ⦋0⦌) a)).2

/-- 概要：関手圏の cofiber 列の右上角は族の右上角を取る関手。
方針：転置の零次成分を計算する。
規約：厳密等号。使われ方：補完した Ar 図式を cofiber 列の頂点として扱う。 -/
lemma cofiberFamilyTriangle_apex {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (cofiberFamilyTriangle H).square 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ cofiberApex C) := by
  change (cofiberFamilySquare H).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [cofiberFamilySquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  rfl

end SerrePositivity.KST.SConstruction
