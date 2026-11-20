module


public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap

/-!
概要：積上の全図式をパラメータ付き関手図式へ移し、元の境界制限と頂点を計算する。
方針：直積の対称性と内部 currying の同型を使う。
規約：元の全図式と全境界制限を厳密な等式で保持する。
使われ方：c5 の実相対商錐回収を、関手圏の固定図式上の slice 比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

def relativeConeProductCurryIso (T S X : SSet.{u}) :
    (ihom (T ⊗ S)).obj X ≅ (ihom T).obj ((ihom S).obj X) :=
  (internalHom.mapIso (β_ S T).op).app X ≪≫ ihomCurryIso S T X

lemma relativeConeProductCurryIso_vertex (T S X : SSet.{u}) (F : T ⊗ S ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso T S X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry ((β_ S T).hom ≫ F)) := rfl

lemma relativeConeProductCurryIso_pre {K T S X : SSet.{u}} (j : K ⟶ T) :
    (pre (j ▷ S)).app X ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso K S X).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso T S X).hom ≫ (pre j).app ((ihom S).obj X) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro k
  apply CategoryTheory.Functor.functorHom_ext
  intro d β
  apply ConcreteCategory.hom_ext
  intro s
  change F.app d (α ≫ β) (j.app d (K.map β k), s) =
    F.app d (α ≫ β) (T.map β (j.app m k), s)
  exact congrArg (fun z : T.obj d => F.app d (α ≫ β) (z, s))
    (ConcreteCategory.congr_hom (j.naturality β) k)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
