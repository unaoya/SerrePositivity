module

public import SerrePositivity.EInfinity.Modules.TensorHomPinched

/-!
# 同じ加群テンソル普遍族の元の augmentation 像

概要：M10 の同じ普遍 Hom 族の全次数像を、元の零次 augmentation 像の定値族へ戻す。
方針：元の augmentation の全自然性を同じ Yoneda・Dold–Kan・pinched 同型で送る。
規約：HA 1.3.1.13、零次の像を明示し、恒等辺との同定は後続で検証する。
使われ方：同じ全 cone と元の augmentation の実三角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の全 augmentation の代表可能 Hom 族は元の零次成分の定値族。
方針：同じ augmentation の全自然性を Yoneda 同値で照合する。
規約：HA 1.3.1.13、同じ元の射。使われ方：普遍評価の元の左脚。 -/
lemma moduleTensorHomRepresentable_augmentation (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleTensorHomRepresentable A D P P n ((moduleTensorSimplicesAugmentation A D P).app n) =
      SSet.const ((moduleTensorSimplicesAugmentation A D P).app ⦋0⦌) := by
  apply SSet.yonedaEquiv.injective
  simp only [moduleTensorHomRepresentable, Equiv.apply_symm_apply]
  change (moduleTensorSimplicesAugmentation A D P).app n =
    ((moduleTensorSimplicesFunctor A D).obj P).map (n.const ⦋0⦌ 0) ≫
      (moduleTensorSimplicesAugmentation A D P).app ⦋0⦌
  have h := (moduleTensorSimplicesAugmentation A D P).naturality (n.const ⦋0⦌ 0)
  exact (h.trans (Category.comp_id _)).symm

/-- 概要：元の零次 augmentation の同じ実 Γ 像。
方針：検証済みの同じ二関手同型の零次成分を使う。
規約：HA 1.3.1.13、同じ頂点。使われ方：元の定値族の指定点。 -/
def moduleTensorAugmentationDoldKanVertex (P : ModuleCategory A D) :
    (((moduleDoldKanHomBifunctor A D).obj (op P)).obj P) _⦋0⦌ :=
  ((((moduleTensorHomDoldKanBifunctorIso A D).app (op P)).app P).hom).app (op ⦋0⦌)
    ((moduleTensorSimplicesAugmentation A D P).app ⦋0⦌)

/-- 概要：元の全 augmentation の実 Γ 像は同じ指定点の定値族。
方針：同じ代表可能族の式を元の全同型で送る。
規約：HA 1.3.1.13、全次数。使われ方：同じ pinched Hom への移送。 -/
lemma moduleTensorHomDoldKanSimplex_augmentation (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleTensorHomDoldKanSimplex A D P P n ((moduleTensorSimplicesAugmentation A D P).app n) =
      SSet.const (moduleTensorAugmentationDoldKanVertex A D P) := by
  dsimp only [moduleTensorHomDoldKanSimplex]
  rw [moduleTensorHomRepresentable_augmentation, SSet.const_comp]
  rfl

private lemma tensorUlift_map_const {K L : SSet.{u}} (z : L _⦋0⦌) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.const (X := K) z) =
      SSet.const (ULift.up z) := rfl

/-- 概要：元の零次 augmentation の同じ pinched Hom 像。
方針：同じ実 Γ 頂点を持ち上げ、元の座標同型で送る。
規約：HA 1.3.1.13、同じ指定点。使われ方：全 cone の元の projection。 -/
def moduleTensorAugmentationPinchedVertex (P : ModuleCategory A D) :
    (PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)) _⦋0⦌ :=
  (moduleDoldKanPinchedIso A D P P).hom.app (op ⦋0⦌)
    (ULift.up (moduleTensorAugmentationDoldKanVertex A D P))

/-- 概要：元の全 augmentation の pinched Hom 像は同じ指定点の定値族。
方針：同じ Γ 像の全等式を元の座標同型で送る。
規約：HA 1.3.1.13、元の全次数。使われ方：全普遍族の augmentation 像。 -/
lemma moduleTensorHomPinchedSimplex_augmentation (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleTensorHomPinchedSimplex A D P P n ((moduleTensorSimplicesAugmentation A D P).app n) =
      SSet.const (moduleTensorAugmentationPinchedVertex A D P) := by
  dsimp only [moduleTensorHomPinchedSimplex]
  rw [moduleTensorHomDoldKanSimplex_augmentation, tensorUlift_map_const, SSet.const_comp]
  rfl

/-- 概要：同じ元の普遍 pinched 族の augmentation 像は同じ定値族。
方針：元の普遍評価式と同じ全 augmentation 像を合成する。
規約：HA 1.3.1.13、元の同じ射。使われ方：全 cone の実三角形の projection。 -/
lemma moduleTensorUniversalPinchedSimplex_augmentation (P : ModuleCategory A D)
    (n : SimplexCategory) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        ((moduleTensorSimplicesAugmentation A D P).app n)) =
    SSet.const (moduleTensorAugmentationPinchedVertex A D P) := by
  exact (moduleTensorUniversalPinchedSimplex_evaluation A D P P n
    ((moduleTensorSimplicesAugmentation A D P).app n)).trans
      (moduleTensorHomPinchedSimplex_augmentation A D P n)

end SerrePositivity.EInfinity.Modules
