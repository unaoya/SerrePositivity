module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNativeValue
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxModel
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRectangle

/-!
概要：元実始域外面の cell 二頂点を、元 LT 外周の始域と lax 中央へ全同値で比較する。
方針：同じ native／ν 同値の逆と元 cell 増大・元 native lax 比較を合成する。
規約：元始域を増大屋根で保持し、resolved 商と元 lax 模型を変更しない。
使われ方：元外周の指定包含・商比較と全二胞体比較の頂点成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d))
local notation "B" => DGOdotGluing R d
local notation "E₀" => dgOdotMilnorSourceCellNativeValueEquivalence R d
local notation "E₁" => dgOdotMilnorCellMiddleNativeValueEquivalence R d

/-- 概要：元実始域の固定 ν 値から元 LT 始域への増大屋根付き指定同値。
方針：同じ元 native／ν 同値の逆に元 cell 増大を合成する。
規約：元 native 始域を保持。使われ方：外周始域の指定頂点比較。 -/
def dgOdotMilnorOuterSourceValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)).obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d).obj :=
  (E₀).symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A))

/-- 概要：元実 cell gluing の固定 ν 値から元 LT lax 中央への指定同値。
方針：元 native／ν 同値の逆・同じ cell 増大・同じ全 lax 比較を合成する。
規約：元実 gluing を保持。使われ方：外周中央の指定頂点比較。 -/
def dgOdotMilnorOuterMiddleValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorCellInput R d)).obj
    (dgOdotMilnorLaxCategory R d).obj :=
  (E₁).symm.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (B)).trans
    (dgOdotMilnorNativeLaxEquivalence R d))

/-- 概要：元始域比較は元 native cell 増大を全関手同型で回収する。
方針：同じ元比較同値の単位二胞体を元増大で写す。
規約：元増大の全単体を保持。使われ方：元始域の増大屋根の成分照合。 -/
def dgOdotMilnorOuterSourceValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((E₀).hom ≫ (dgOdotMilnorOuterSourceValueEquivalence R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A)).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((E₀).hom ≫ ((E₀).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A)).hom)) _
  rw [← Category.assoc]
  simpa only [Category.id_comp] using
    ((E₀).homInvIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A)).hom)

/-- 概要：元中央比較は元 native cell 増大と同じ lax 比較の合成を回収する。
方針：同じ元比較同値の単位二胞体を元合成で写す。
規約：元増大・元全 lax 比較を保持。使われ方：実外周二辺の全自然性。 -/
def dgOdotMilnorOuterMiddleValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((E₁).hom ≫ (dgOdotMilnorOuterMiddleValueEquivalence R d).hom)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (B)).hom ≫
      (dgOdotMilnorNativeLaxEquivalence R d).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((E₁).hom ≫ ((E₁).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (B)).hom ≫
      (dgOdotMilnorNativeLaxEquivalence R d).hom))) _
  rw [← Category.assoc]
  simpa only [Category.id_comp] using ((E₁).homInvIso.postcomp
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (B)).hom ≫
      (dgOdotMilnorNativeLaxEquivalence R d).hom))

/-- 概要：元始域屋根の指定同値を同じ完全射にする。
方針：元全同値の完全性を束ねる。規約：同じ順方向を保持。
使われ方：外周包含辺の全比較の始域成分。 -/
def dgOdotMilnorOuterSourceComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d) :=
  ⟨(dgOdotMilnorOuterSourceValueEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence⟩

/-- 概要：元中央の指定同値を同じ完全射にする。
方針：元全同値の完全性を束ねる。規約：同じ順方向を保持。
使われ方：外周包含・商辺で共有する中央成分。 -/
def dgOdotMilnorOuterMiddleComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorCellInput R d)) (dgOdotMilnorLaxCategory R d) :=
  ⟨(dgOdotMilnorOuterMiddleValueEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence⟩
end SerrePositivity.KST.SConstruction
