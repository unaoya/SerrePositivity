module
public import SerrePositivity.KST.SConstruction.SExactValues
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.ExactEnrichment
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity

/-! # 全完全関手族による元の S_n の作用
概要：完全関手空間の全単体が、元の全 gapped S_n に作用する。
方針：内部 Hom の実合成を、各入力頂点の cofiber 保存で gapped 部分複体へ持ち上げる。
規約：自然変換を頂点に潰さない。使われ方：厳密豊穣 S• と元の通常作用の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 元の gapped 図式と全完全関手族を合成する、全単体の実 S_n 作用。 -/
def sExactFamilyAction (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    sConstruction n C.obj ⊗ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}) ⟶ sConstruction n D.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _
    (((gappedSubcomplex n C.obj).ι ⊗ₘ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι) ≫
      MonoidalClosed.comp (arNerve n) C.obj D.obj) (by
    intro v
    let F := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv C D).symm v.2
    let G := gappedDiagram v.1
    have hF : v.2.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv C D).apply_symm_apply v.2).symm
    have hG : v.1.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C.obj).apply_symm_apply _ |>.symm
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D.obj).symm
      ((MonoidalClosed.comp (arNerve n) C.obj D.obj).app _ (v.1.val, v.2.val)))
    rw [hF, hG, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.internalComp_vertex]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _) (G ≫ F.hom)))
    rw [Equiv.symm_apply_apply]
    exact IsGapped.postcomp_of_cofiber (gappedDiagram_isGapped v.1) F.hom
      (preservesCofiberData_of_isExactFunctor F.hom))

/-- 元の図式空間の包含の後では、同じ実内部 Hom 合成を回収する。 -/
lemma sExactFamilyAction_inclusion (n : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    sExactFamilyAction n C D ≫ (gappedSubcomplex n D.obj).ι =
      ((gappedSubcomplex n C.obj).ι ⊗ₘ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι) ≫
        MonoidalClosed.comp (arNerve n) C.obj D.obj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の完全射に固定すると、同じ元の cofiber 型 S_n 後合成を全単体で回収する。 -/
lemma sExactFamilyAction_fixed (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    (𝟙 (sConstruction n C.obj) ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F) ≫ sExactFamilyAction n C D =
      (ρ_ (sConstruction n C.obj)).hom ≫
        sPostcompCofiber n F.hom (preservesCofiberData_of_isExactFunctor F.hom) := by
  apply (cancel_mono (gappedSubcomplex n D.obj).ι).mp
  erw [Category.assoc, sExactFamilyAction_inclusion, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι]
  erw [tensorHom_def, Category.assoc, whiskerLeft_curry'_comp,
    ← Category.assoc, rightUnitor_naturality]

end SerrePositivity.KST.SConstruction
