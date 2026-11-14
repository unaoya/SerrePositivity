module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-! # 同じ実逆射を比較ホモトピーに沿って輸送する

概要：元の実逆射と両往復ホモトピーを、射の実比較ホモトピーに沿って輸送する。
方針：比較を同じ逆射で前後合成し、既存の往復ホモトピーと合成する。
規約：逆射を選び直さず、モデル構造の仮定を追加しない。
使われ方：導来係数比較の実逆射を正本の Hom 比較へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
def dgGluingHomotopyInverseTransportUnit {A B : SSet.{u}} [Quasicategory A]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (i : B ⟶ A)
    (hA : SSet.Homotopy (g ≫ i) (𝟙 A)) : SSet.Homotopy (f ≫ i) (𝟙 A) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyComposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H i) hA

def dgGluingHomotopyInverseTransportCounit {A B : SSet.{u}} [Quasicategory B]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (i : B ⟶ A)
    (hB : SSet.Homotopy (i ≫ g) (𝟙 B)) : SSet.Homotopy (i ≫ f) (𝟙 B) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyComposite (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) hB

lemma dgGluingHomotopyInverse_transport {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (i : B ⟶ A)
    (hA : SSet.Homotopy (g ≫ i) (𝟙 A)) (hB : SSet.Homotopy (i ≫ g) (𝟙 B)) :
    Nonempty (SSet.Homotopy (f ≫ i) (𝟙 A)) ∧
      Nonempty (SSet.Homotopy (i ≫ f) (𝟙 B)) :=
  ⟨⟨dgGluingHomotopyInverseTransportUnit H i hA⟩,
    ⟨dgGluingHomotopyInverseTransportCounit H i hB⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
