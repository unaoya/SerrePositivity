module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing

/-! 端点表示の等式輸送は実ホモトピーの全円柱写像を変更しない。 -/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet

lemma dgGluingHomotopyRetarget_h {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H hf hg).h = H.h := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
