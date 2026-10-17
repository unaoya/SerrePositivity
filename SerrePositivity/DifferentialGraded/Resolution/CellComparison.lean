module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapAugmentation
public import SerrePositivity.DifferentialGraded.Resolution.CellCategory

/-! # dg関手に沿うcell反復列と最終解像度の比較

## 概要
dg関手に沿うcell反復列と最終解像度の比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def stageComparison : (n : ℕ) →
    FixedObjectAugmentation.Map (stage A D n) (stage A E n) F
  | 0 => initialComparison A D E F
  | n + 1 => (stageComparison n).attach

lemma transition_comparison (n : ℕ) (x y : D) :
    transition A D n x y ≫ (stageComparison A D E F (n + 1)).hom x y =
      (stageComparison A D E F n).hom x y ≫ transition A E n (F.obj x) (F.obj y) :=
  (stageComparison A D E F n).transition_attachedHom x y

def comparisonCocone (x y : D) : Cocone (homDiagram A D x y) where
  pt := candidateHom A E (F.obj x) (F.obj y)
  ι := NatTrans.ofSequence
    (fun n => (stageComparison A D E F n).hom x y ≫
      stageInclusion A E n (F.obj x) (F.obj y)) (fun n => by
      change (homDiagram A D x y).map (homOfLE (Nat.le_succ n)) ≫
        ((stageComparison A D E F (n + 1)).hom x y ≫
          stageInclusion A E (n + 1) (F.obj x) (F.obj y)) =
        ((stageComparison A D E F n).hom x y ≫
          stageInclusion A E n (F.obj x) (F.obj y)) ≫ 𝟙 _
      dsimp only [homDiagram]
      rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
      change transition A D n x y ≫
        ((stageComparison A D E F (n + 1)).hom x y ≫
          stageInclusion A E (n + 1) (F.obj x) (F.obj y)) = _
      rw [← Category.assoc, transition_comparison, Category.assoc, transition_inclusion])

def comparisonHom (x y : D) :
    candidateHom A D x y ⟶ candidateHom A E (F.obj x) (F.obj y) :=
  colimit.desc _ (comparisonCocone A D E F x y)

@[reassoc] lemma stageInclusion_comparison (n : ℕ) (x y : D) :
    stageInclusion A D n x y ≫ comparisonHom A D E F x y =
      (stageComparison A D E F n).hom x y ≫ stageInclusion A E n (F.obj x) (F.obj y) :=
  colimit.ι_desc _ _

lemma comparisonHom_augmentation (x y : D) :
    comparisonHom A D E F x y ≫ candidateAugmentation A E (F.obj x) (F.obj y) =
      candidateAugmentation A D x y ≫ F.map x y := by
  apply colimit.hom_ext
  intro n
  change stageInclusion A D n x y ≫ _ = stageInclusion A D n x y ≫ _
  rw [← Category.assoc, stageInclusion_comparison, Category.assoc,
    stageInclusion_augmentation, ← Category.assoc, stageInclusion_augmentation]
  exact (stageComparison A D E F n).augmentation x y

lemma comparisonHom_unit (x : D) :
    candidateUnit A D x ≫ comparisonHom A D E F x x = candidateUnit A E (F.obj x) := by
  rw [candidateUnit, Category.assoc, stageInclusion_comparison,
    ← Category.assoc, (stageComparison A D E F 0).map_id]
  rfl

lemma comparisonHom_comp (x y z : D) :
    candidateComposition A D x y z ≫ comparisonHom A D E F x z =
      (comparisonHom A D E F x y ⊗ₘ comparisonHom A D E F y z) ≫
        candidateComposition A E (F.obj x) (F.obj y) (F.obj z) := by
  apply (candidateTensorIsColimit A D x y z).hom_ext
  intro n
  change (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫
    (candidateComposition A D x y z ≫ comparisonHom A D E F x z) =
    (stageInclusion A D n x y ⊗ₘ stageInclusion A D n y z) ≫
      ((comparisonHom A D E F x y ⊗ₘ comparisonHom A D E F y z) ≫ _)
  rw [← Category.assoc, candidateComposition_stage, Category.assoc,
    stageInclusion_comparison, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
    stageInclusion_comparison, stageInclusion_comparison, ← tensorHom_comp_tensorHom,
    (stageComparison A D E F n).map_comp]
  simp only [Category.assoc]
  rw [candidateComposition_stage]

/-- 最終増大の厳密な可換squareを伴う比較。 -/
def comparison : FixedObjectAugmentation.Map (candidate A D) (candidate A E) F where
  hom := comparisonHom A D E F
  map_id := comparisonHom_unit A D E F
  map_comp := comparisonHom_comp A D E F
  augmentation := comparisonHom_augmentation A D E F

def comparisonFunctor : DGFunctor A (Source A D) (Source A E) :=
  (comparison A D E F).toDGFunctor

lemma comparisonFunctor_augmentation :
    (comparisonFunctor A D E F).comp (augmentation A E) = (augmentation A D).comp F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (comparisonFunctor A D E F).comp (augmentation A E))
    (G := (augmentation A D).comp F) (fun _ => rfl)
  intro x y
  change (comparisonHom A D E F x.val y.val ≫
    candidateAugmentation A E (F.obj x.val) (F.obj y.val)) ≫ eqToHom (by rfl) = _
  rw [eqToHom_refl, Category.comp_id, comparisonHom_augmentation]
  rfl

lemma comparisonHom_quasiIso (hF : HomQuasiIso F) (x y : D) :
    QuasiIso (comparisonHom A D E F x y) := by
  let : QuasiIso (F.map x y) := hF x y
  let : QuasiIso (candidateAugmentation A D x y) :=
    candidateAugmentation_quasiIso A D x y
  let : QuasiIso (candidateAugmentation A E (F.obj x) (F.obj y)) :=
    candidateAugmentation_quasiIso A E (F.obj x) (F.obj y)
  have : QuasiIso (comparisonHom A D E F x y ≫
      candidateAugmentation A E (F.obj x) (F.obj y)) := by
    rw [comparisonHom_augmentation]
    infer_instance
  exact quasiIso_of_comp_right _ (candidateAugmentation A E (F.obj x) (F.obj y))

lemma comparisonFunctor_homQuasiIso (hF : HomQuasiIso F) :
    HomQuasiIso (comparisonFunctor A D E F) :=
  fun x y => comparisonHom_quasiIso A D E F hF x.val y.val

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
