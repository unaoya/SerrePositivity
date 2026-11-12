module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationHomLifting
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomWhiskering

/-!
概要：元の頂点等式で正規化した Hom 作用の合成と、指定自然同型の可換正方形。
方針：端点の等式を消去して元の関手の Hom 作用と自然性へ帰着する。
規約：指定した全自然同型の成分を使う。
使われ方：P-12 の分類 Hom と底変換の正規化された可換正方形。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：正規化した二つの Hom 作用の合成は同じ合成写像の正規化と一致する。
方針：指定端点等式を消去し、ホモトピー圏への関手の合成則を使う。
規約：中間の元の頂点を保持する。使われ方：分類と底変換の二順序の比較。 -/
lemma normalizedVertexHomMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {x y : X _⦋0⦌} {x₁ y₁ : Y _⦋0⦌} {x₂ y₂ : Z _⦋0⦌}
    (hx : x₁ = f.app (Opposite.op ⦋0⦌) x) (hy : y₁ = f.app (Opposite.op ⦋0⦌) y)
    (hX : x₂ = g.app (Opposite.op ⦋0⦌) x₁) (hY : y₂ = g.app (Opposite.op ⦋0⦌) y₁)
    (a : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap g hX hY (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap f hx hy a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap (f ≫ g)
        (hX.trans (congrArg (g.app (Opposite.op ⦋0⦌)) hx))
        (hY.trans (congrArg (g.app (Opposite.op ⦋0⦌)) hy)) a := by
  subst x₁
  subst y₁
  subst x₂
  subst y₂
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hoFunctor_map_comp_apply f g a).symm

/-- 概要：指定自然同型の元の成分を、指定された両頂点へ輸送する。
方針：同じ成分の前後に元の頂点等式の同型を合成する。
規約：自然同型を選び直さない。使われ方：分類の底変換同型の同じ成分の表示。 -/
def normalizedFunctorIsoComponent {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : X _⦋0⦌)
    {xf xg : Y _⦋0⦌}
    (hf : xf = f.app (Opposite.op ⦋0⦌) x) (hg : xg = g.app (Opposite.op ⦋0⦌) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso xf xg :=
  eqToIso (congrArg HomotopyCategory.mk hf) ≪≫ e.app x ≪≫
    (eqToIso (congrArg HomotopyCategory.mk hg)).symm

/-- 概要：指定自然同型の正規化した成分は、同じ正規化した全 Hom 作用と可換。
方針：両端点の等式を消去して元の自然同型の自然性を適用する。
規約：元の射 a と指定された同型 e を保持する。
使われ方：分類と底変換の実 Hom 正方形の主な自然性。 -/
lemma normalizedVertexHomMap_naturality {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    {x y : X _⦋0⦌} {xf yf xg yg : Y _⦋0⦌}
    (hxf : xf = f.app (Opposite.op ⦋0⦌) x) (hyf : yf = f.app (Opposite.op ⦋0⦌) y)
    (hxg : xg = g.app (Opposite.op ⦋0⦌) x) (hyg : yg = g.app (Opposite.op ⦋0⦌) y)
    (a : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap f hxf hyf a ≫ (normalizedFunctorIsoComponent e y hyf hyg).hom =
      (normalizedFunctorIsoComponent e x hxf hxg).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap g hxg hyg a := by
  subst xf
  subst yf
  subst xg
  subst yg
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap, normalizedFunctorIsoComponent, eqToHom_refl,
    eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl, Category.id_comp, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app, Iso.app_hom, hoFunctor_map, Functor.toCatHom_toFunctor,
    mapHomotopyCategory_obj_mk] using e.toNatIso.hom.naturality a

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
