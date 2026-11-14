module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskerHEq
/-!
概要：同じ双加群射の像と準同型性を、実分解後の可逆性へ接続する。
方針：元の評価射・全 Hom 自然性・型付きの射の一致を保持する。
規約：出力の射影性と原 Hom の平坦性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
lemma functorHom_isIso_of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (hab : HEq a b) (hb : IsIso b) : IsIso a := by
  subst f' g'
  cases eq_of_heq hab
  exact hb
lemma functorHomPostcomp_heq {X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (hab : HEq a b) (H : Y ⟶ Z) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g H a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f' g' H b) := by
  subst f' g'
  cases eq_of_heq hab
  rfl
lemma functorHomPostcomp_isIso_of_heq {X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (hab : HEq a b) (H : Y ⟶ Z) (hb : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f' g' H b)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g H a) := by
  exact functorHom_isIso_of_heq _ _ (congrArg (fun q => q ≫ H) hf)
    (congrArg (fun q => q ≫ H) hg) (functorHomPostcomp_heq a b hf hg hab H) hb
end SerrePositivity.InfinityCategories.Project.DerivedCategories
