module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Sheaves.PresheafElementsSiteLift
public import SerrePositivity.InfinityCategories.Sheaves.AsSmallSiteShape

/-!
概要：同じsiteと値の宇宙持ち上げに沿って、元の要素圏の全nerveを厳密に移す。
方針：各合成可能射列へ指定したsiteLiftElementsUp・Downを後合成する。
規約：HTT 5.1.5.6、Kerodon §7.1（Tag 02H1）の重み付き切断に使う既存構成の宇宙移送の法則。
  小さい通常のsiteの集合値重みの表示に限る。別の小さい模型は選ばない。
使われ方：5∞-1の残り第10項、元の切断錐とその制限を同じ形状同型で運ぶ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 同じ要素のup/downを全単体へ送る、指定した厳密な形状同型。 -/
@[cite HTT "5.1.5.6" (partial := special) "小さい通常siteの集合値重みの要素圏の宇宙移送。"]
def siteLiftElementsShapeIso (P : Cᵒᵖ ⥤ Type u) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve P.Elements) ≅
      nerve (siteLiftPresheaf P).Elements where
  hom :=
    { app := fun _ => ↾fun σ => σ.down ⋙ siteLiftElementsUp P
      naturality := fun _ _ _ => rfl }
  inv :=
    { app := fun _ => ↾fun σ => ULift.up (σ ⋙ siteLiftElementsDown P)
      naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 指定形状同型は、元の前層の同じ射の要素圏への作用と可換。 -/
lemma siteLiftElementsShapeIso_naturality {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    (siteLiftElementsShapeIso P).hom ≫ nerveMap (siteLiftPresheafMap φ).mapElements =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
        (siteLiftElementsShapeIso Q).hom := rfl

end SerrePositivity.InfinityCategories.Sheaves
