module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceModel
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate
public import SerrePositivity.KST.SConstruction.DGModuleExtensionComposition
/-!
概要：小さい出発提示を保持する模型に実 dg 延長の作用を与える。
方針：出発圏・seed を固定して関手ラベルだけを後合成し、元の実合成比較で共役する。
規約：全 Hom 複体を使う。厳密法則は比較の三角・結合式との照合後に主張する。
使われ方：16時間試作の厳密関手的な提示模型の固定入力作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u}) (F : DGFunctor R D E)

def dgKappaPresentedSourceActionIso (X : DGKappaPresentedSourceObject R D κ) :=
  dgModuleExtensionCompositionAt R (X.code.Objects R κ) D E X.arrow F
    (ForgetEnrichment.to (Complex R) (dgKappaPresentedSourceSeed R D κ X))

def dgKappaPresentedSourceAction :
    DGFunctor R (DGKappaPresentedSourceObject R D κ) (DGKappaPresentedSourceObject R E κ) :=
  inducedDGFunctorClosedConjugate R
    (dgKappaPresentedSourceValue R D κ) (dgKappaPresentedSourceValue R E κ)
    (dgModuleExtension R D E F) (dgKappaPresentedSourceObjectMap R D κ E F)
    (dgKappaPresentedSourceActionIso R D E κ F)

lemma dgKappaPresentedSourceAction_map (X Y : DGKappaPresentedSourceObject R D κ) :
    (dgKappaPresentedSourceAction R D E κ F).map X Y =
      (dgModuleExtension R D E F).map
        (dgKappaPresentedSourceValue R D κ X) (dgKappaPresentedSourceValue R D κ Y) ≫
          enrichedClosedIsoConjugation (Complex R)
            (dgKappaPresentedSourceActionIso R D E κ F X)
            (dgKappaPresentedSourceActionIso R D E κ F Y) := by
  change (𝟙 _ ≫ _) ≫ _ = _
  rw [Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories
