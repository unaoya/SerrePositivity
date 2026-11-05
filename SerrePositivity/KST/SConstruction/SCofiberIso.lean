module
public import SerrePositivity.KST.SConstruction.SCofiberInverse

/-! # S_n と cofiber 図式の厳密な交換同型
概要：二方向の転置は全 gapped 図式と全 cofiber 四角形を厳密に回収する。
方針：二重内部 Hom の単射な包含で二回の交換を計算する。
規約：同値の選択や零対象の正規化に依存しない。使われ方：加法性の有限反復。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 順方向の転置の二重包含による厳密な式。 -/
lemma sCofiberComparison_double_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (sCofiberComparison n C ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι =
    ((gappedSubcomplex n (cofiberDiagrams C)).ι ≫
      (ihom (arNerve n)).map (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      (internalHomSwapIso (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C).hom := by
  rw [sCofiberComparison_ι, sCofiberTransposeSquare_ι]
  rfl

/-- 逆方向の転置の二重包含による厳密な式。 -/
lemma sCofiberInverse_double_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    (sCofiberInverse n C ≫ (gappedSubcomplex n (cofiberDiagrams C)).ι) ≫
      (ihom (arNerve n)).map (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
    ((fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι) ≫
      (internalHomSwapIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom := by
  rw [sCofiberInverse_ι, sCofiberInverseDiagram_ι]
  rfl

/-- 単射な二つの表示上で互いに逆な交換と可換な射対は元でも片側逆。 -/
lemma inverse_comp_of_commuting_mono {A B R S : SSet.{u}}
    (a : A ⟶ R) [Mono a] (b : B ⟶ S) (f : A ⟶ B) (g : B ⟶ A)
    (s : R ⟶ S) (t : S ⟶ R) (hf : f ≫ b = a ≫ s) (hg : g ≫ a = b ≫ t)
    (hst : s ≫ t = 𝟙 R) : f ≫ g = 𝟙 A := by
  apply (cancel_mono a).1
  calc
    (f ≫ g) ≫ a = f ≫ (g ≫ a) := Category.assoc _ _ _
    _ = f ≫ (b ≫ t) := congrArg (fun k => f ≫ k) hg
    _ = (f ≫ b) ≫ t := (Category.assoc _ _ _).symm
    _ = (a ≫ s) ≫ t := congrArg (fun k => k ≫ t) hf
    _ = a ≫ (s ≫ t) := Category.assoc _ _ _
    _ = a ≫ 𝟙 R := congrArg (fun k => a ≫ k) hst
    _ = 𝟙 A ≫ a := (Category.comp_id a).trans (Category.id_comp a).symm

/-- cofiber 値の全 gapped 図式は二回の転置で厳密に回収される。 -/
lemma sCofiberComparison_inverse (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    sCofiberComparison n C ≫ sCofiberInverse n C = 𝟙 _ := by
  let i := (gappedSubcomplex n (cofiberDiagrams C)).ι
  let j := (ihom (arNerve n)).map
    (fullSubcomplexOnVertices _ (IsCofiberDiagramVertex (C := C))).ι
  let k := (fullSubcomplexOnVertices _
    (IsCofiberDiagramVertex (C := sConstruction n C))).ι
  let l := (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι
  have : Mono j := (ihom (arNerve n)).map_mono _
  apply inverse_comp_of_commuting_mono (i ≫ j) (k ≫ l)
    (sCofiberComparison n C) (sCofiberInverse n C)
    (internalHomSwapIso (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C).hom
    (internalHomSwapIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom
  · exact (Category.assoc _ _ _).symm.trans (sCofiberComparison_double_ι n C)
  · exact (Category.assoc _ _ _).symm.trans (sCofiberInverse_double_ι n C)
  · exact _root_.SerrePositivity.InfinityCategories.Kan.internalHomSwap_twice _ _ _

/-- S_n 内の全 cofiber 四角形も二回の転置で厳密に回収される。 -/
lemma sCofiberInverse_comparison (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    sCofiberInverse n C ≫ sCofiberComparison n C = 𝟙 _ := by
  let i := (fullSubcomplexOnVertices _
    (IsCofiberDiagramVertex (C := sConstruction n C))).ι
  let j := (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι
  let k := (gappedSubcomplex n (cofiberDiagrams C)).ι
  let l := (ihom (arNerve n)).map
    (fullSubcomplexOnVertices _ (IsCofiberDiagramVertex (C := C))).ι
  have : Mono j := (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map_mono _
  apply inverse_comp_of_commuting_mono (i ≫ j) (k ≫ l)
    (sCofiberInverse n C) (sCofiberComparison n C)
    (internalHomSwapIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom
    (internalHomSwapIso (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C).hom
  · exact (Category.assoc _ _ _).symm.trans (sCofiberInverse_double_ι n C)
  · exact (Category.assoc _ _ _).symm.trans (sCofiberComparison_double_ι n C)
  · exact _root_.SerrePositivity.InfinityCategories.Kan.internalHomSwap_twice _ _ _

/-- 全 gapped 図式の S_n は全 cofiber 四角形の構成と厳密に交換する。 -/
def sCofiberIso (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    sConstruction n (cofiberDiagrams C) ≅ cofiberDiagrams (sConstruction n C) where
  hom := sCofiberComparison n C
  inv := sCofiberInverse n C
  hom_inv_id := sCofiberComparison_inverse n C
  inv_hom_id := sCofiberInverse_comparison n C

end SerrePositivity.KST.SConstruction
