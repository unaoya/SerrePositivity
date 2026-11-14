module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeObject

/-!
cone 対象候補の augmentation と元の実 cone 比較射を、全 dg 自然なホモトピーで接続する。
右代表の移送は通常 tensor の H⁰ 作用と実加群同型の合成として保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C A.left B.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D A.right B.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)))

/-- 元の左代表加群の cone を始域に保つ、右代表への移送後の実比較射。 -/
def dgGluingConeAugmentationCore :
    moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt q.obj) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M A B f ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)).hom ≫
    (Morita.kernelTensor R D C M).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R D A.right B.right
        ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)) q) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).hom

/-- 左代表への移送は、同じ実 cone 比較射との全 dg 自然なホモトピーを持つ。 -/
lemma dgGluingConeAugmentation_transport :
    Nonempty (ModuleHomotopy R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R C A.left B.left
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f) p ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeAugmentation R C D M A B f p q)
      (dgGluingConeAugmentationCore R C D M A B f q)) := by
  apply (moduleToHomotopy_map_eq_iff R C _ _).1
  change (moduleToHomotopy R C).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R C A.left B.left
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f) p ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeInv R C A.left B.left
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f) p ≫
          dgGluingConeAugmentationCore R C D M A B f q)) = _
  simp only [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom_map,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeInv_map, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 構成した gluing 対象の augmentation 自身についても、同じ実ホモトピーを回収する。 -/
lemma dgGluingConeObject_augmentation_transport :
    Nonempty (ModuleHomotopy R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R C A.left B.left
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f) p ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M A B f p q))
      (dgGluingConeAugmentationCore R C D M A B f q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject_augmentation]
  exact dgGluingConeAugmentation_transport R C D M A B f p q

/-- 右代表の移送は K(C) でも元の実 cone と同型である。 -/
def dgGluingConeRightHomotopyIso :
    (moduleToHomotopy R C).obj (moduleCone R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f))) ≅
    (moduleToHomotopy R C).obj
      (ForgetEnrichment.of (Complex R) (M.rightAt q.obj)) :=
  (moduleToHomotopy R C).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso R C D M
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)) ≪≫
  (Morita.kernelTensor R D C M).onHomotopy.mapIso q.comparison ≪≫
  (moduleToHomotopy R C).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj))

/-- 選んだ実右代表射の tensor 像は、同じ K(D) の代表同型の H⁰ 作用を回収する。 -/
lemma dgGluingConeRightRepresentativeHom_map :
    (moduleToHomotopy R C).map ((Morita.kernelTensor R D C M).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R D A.right B.right
        ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)) q)) =
    (Morita.kernelTensor R D C M).onHomotopy.map q.comparison.hom := by
  have h := congrArg (fun t ↦ (Morita.kernelTensor R D C M).onHomotopy.map t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom_map R D A.right B.right
      ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)) q)
  exact h

/-- 移送後の実比較射の K(C) の像は、元の cone 比較射と同じ右移送同型の合成。 -/
lemma dgGluingConeAugmentationCore_hom :
    (moduleToHomotopy R C).map (dgGluingConeAugmentationCore R C D M A B f q) =
    (moduleToHomotopy R C).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M A B f) ≫
      (dgGluingConeRightHomotopyIso R C D M A B f q).hom := by
  simp only [dgGluingConeAugmentationCore, dgGluingConeRightHomotopyIso,
    Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom]
  rw [dgGluingConeRightRepresentativeHom_map]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
