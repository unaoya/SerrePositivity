module
public import SerrePositivity.KST.Fibration.RelativeSKernelSimplicialIso
public import SerrePositivity.KST.Fibration.RelativeSQuotientRealization
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagrams

/-!
概要：零圏への指定完全関手による、全 S• から core S• への実写像。
方針：全対象の零性で相対条件を自動化し、元の相対商射影を使う。
規約：指定関手と core 包含を厳密に保持する。
使われ方：商核四角形の零角を、指定 Verdier 四角形の左辺へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 零圏への指定関手では、全ての gapped S 図式が相対条件を満たす。 -/
lemma relativeS_eq_top_of_zeroTarget {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) (n : ℕ) :
    relativeSConstruction f.hom n = ⊤ :=
  relativeDiagram_eq_top_of_zero f.hom (sComponentEvaluation A.obj n)
    (fun _ _ => hZ _)

/-- 零圏への相対 S_n は、包含を順射とする全 S_n との同型を持つ。 -/
def relativeSZeroTargetTopIso {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) (n : ℕ) :
    (relativeSConstruction f.hom n : SSet.{u}) ≅ sConstruction n A.obj :=
  eqToIso (congrArg (fun Q : (sConstruction n A.obj).Subcomplex => (Q : SSet.{u}))
    (relativeS_eq_top_of_zeroTarget f hZ n)) ≪≫ Subcomplex.topIso _

/-- この同型の順射は、同じ相対部分複体の元の包含。 -/
lemma relativeSZeroTargetTopIso_hom {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) (n : ℕ) :
    (relativeSZeroTargetTopIso f hZ n).hom = (relativeSConstruction f.hom n).ι :=
  subcomplexTopIso_hom_inclusion _ (relativeS_eq_top_of_zeroTarget f hZ n)

/-- 元の包含を保つ段ごとの同型は、全ての面・退化と可換。 -/
def relativeSZeroTargetSimplicialIso {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    relativeSimplicialSConstruction f.hom ≅ simplicialSConstruction A.obj :=
  NatIso.ofComponents (fun n => relativeSZeroTargetTopIso f hZ n.unop.len)
    (fun θ => by
      change _ ≫ (relativeSZeroTargetTopIso f hZ _).hom =
        (relativeSZeroTargetTopIso f hZ _).hom ≫ _
      rw [relativeSZeroTargetTopIso_hom, relativeSZeroTargetTopIso_hom]
      rfl)

/-- 零圏への指定関手は、全 S• から零圏の core S• へ作用する。 -/
def zeroTargetFullSMap {A Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    simplicialSConstruction A.obj ⟶
      simplicialSConstruction Z.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  (relativeSZeroTargetSimplicialIso f hZ).inv ≫ relativeSimplicialQuotientMap f

/-- 元の相対図式から零角への比較は、core 上で指定完全関手を厳密に回収する。 -/
theorem zeroTargetFullSMap_core {A B Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : A.obj ⟶ B.obj) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    relativeSimplicialSConstructionCoreInclusion q ≫
        relativeSimplicialSConstructionInclusion q ≫
        zeroTargetFullSMap f hZ = coreSExactMap f := by
  have hi : relativeSimplicialSConstructionCoreInclusion q ≫
        relativeSimplicialSConstructionInclusion q =
      relativeSimplicialSConstructionCoreInclusion f.hom ≫
        (relativeSZeroTargetSimplicialIso f hZ).hom := by
    apply NatTrans.ext
    funext n
    change _ = _ ≫ (relativeSZeroTargetTopIso f hZ n.unop.len).hom
    rw [relativeSZeroTargetTopIso_hom]
    rfl
  rw [← Category.assoc, hi]
  dsimp only [zeroTargetFullSMap]
  rw [Category.assoc, ← Category.assoc (relativeSZeroTargetSimplicialIso f hZ).hom,
    Iso.hom_inv_id, Category.id_comp, relativeSimplicialQuotientMap_core]

/-- 相対核の元の全 S 図式に、指定した零値完全関手を作用させる比較。 -/
def relativeSZeroTargetCornerMap {A B Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : A.obj ⟶ B.obj) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    relativeSimplicialSConstruction q ⟶
      simplicialSConstruction Z.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  relativeSimplicialSConstructionInclusion q ≫ zeroTargetFullSMap f hZ

/-- 零角比較は、元の相対核への左辺と指定した core S• 左辺を厳密に結ぶ。 -/
theorem relativeSZeroTargetCornerMap_left {A B Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : A.obj ⟶ B.obj) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    relativeSimplicialSConstructionCoreInclusion q ≫
        relativeSZeroTargetCornerMap q f hZ = coreSExactMap f :=
  zeroTargetFullSMap_core q f hZ

/-- 同じ零角比較の実現も、指定した左辺の実現射を厳密に回収する。 -/
theorem relativeSZeroTargetCornerMap_realization_left {A B Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : A.obj ⟶ B.obj) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q) ≫
        simplicialDiagonalFunctor.map (relativeSZeroTargetCornerMap q f hZ) =
      simplicialDiagonalFunctor.map (coreSExactMap f) := by
  rw [← Functor.map_comp, relativeSZeroTargetCornerMap_left]

end SerrePositivity.KST.Fibration
