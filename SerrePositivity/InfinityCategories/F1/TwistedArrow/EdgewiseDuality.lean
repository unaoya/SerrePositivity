module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseWeightDuality

/-!
概要：単体集合とその反転の edgewise subdivision の自然な同型。
方針：重みからの射を反転し、重みの自己反転同型の逆で前合成する。
規約：同型性は各次数の射の型の全単射から得る。
使われ方：Kerodon Remark 8.1.1.7、Corollary 5.6.0.6、両端射影の同値の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合の edgewise subdivision を反転した単体集合のものへ写す双対写像。
方針：各重みからの射を opFunctor で写し、重みの逆反転で始域を戻す。
規約：元の単体集合に Kan 性は要求しない。
使われ方：Kerodon Remark 8.1.1.7、左射影を反転後の右射影へ移す写像。 -/
noncomputable def edgewiseDuality (X : SSet.{u}) : edgewiseSubdivision X ⟶ edgewiseSubdivision X.op where
  app n := ↾fun f ↦ (edgewiseWeightReverseIso n.unop).inv ≫ SSet.opFunctor.map f
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro f
    change (edgewiseWeightReverseIso m.unop).inv ≫
      SSet.opFunctor.map (edgewiseWeight.map α.unop ≫ f) =
      edgewiseWeight.map α.unop ≫ (edgewiseWeightReverseIso n.unop).inv ≫ SSet.opFunctor.map f
    rw [SSet.opFunctor.map_comp, ← Category.assoc,
      ← edgewiseWeightReverse_inv_naturality, Category.assoc]

/-- 概要：edgewise の双対写像は同型。
方針：opFunctor の Hom の全単射と重みの同型による前合成の全単射を各次数で合成する。
規約：逆写像の式を選び直すことなく全単射性で証明する。
使われ方：Kerodon Remark 8.1.1.7、左射影の持ち上げ性の同型による移送。 -/
instance edgewiseDuality_isIso (X : SSet.{u}) : IsIso (edgewiseDuality X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  have hp : Function.Bijective (fun g : (edgewiseWeight.{u}.obj n.unop).op ⟶ X.op ↦
      (edgewiseWeightReverseIso n.unop).inv ≫ g) := by
    constructor
    · intro g h he
      exact (cancel_epi (edgewiseWeightReverseIso n.unop).inv).1 he
    · intro g
      refine ⟨(edgewiseWeightReverseIso n.unop).hom ≫ g, ?_⟩
      change (edgewiseWeightReverseIso n.unop).inv ≫
        ((edgewiseWeightReverseIso n.unop).hom ≫ g) = g
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have ho : Function.Bijective (fun f : edgewiseWeight.obj n.unop ⟶ X ↦ SSet.opFunctor.map f) :=
    SSet.opEquivalence.fullyFaithfulFunctor.homEquiv.bijective
  exact hp.comp ho

/-- 概要：単体集合とその反転の edgewise subdivision の標準同型。
方針：双対写像の同型性を束ねる。
規約：順方向は edgewiseDuality。
使われ方：Kerodon Remark 8.1.1.7、反転比較の共通始域の同定。 -/
noncomputable def edgewiseDualityIso (X : SSet.{u}) : edgewiseSubdivision X ≅ edgewiseSubdivision X.op :=
  asIso (edgewiseDuality X)

/-- 概要：edgewise の双対写像は単体集合の射に関して自然。
方針：元の射と後続の射の反転が合成を保つことを使う。
規約：標的の射には opFunctor を施す。
使われ方：Kerodon Remark 8.1.1.7、Kan 値の図式全体で自然な反転比較。 -/
lemma edgewiseDuality_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewiseSubdivisionMap f ≫ edgewiseDuality Y =
      edgewiseDuality X ≫ edgewiseSubdivisionMap (SSet.opFunctor.map f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  change (edgewiseWeightReverseIso n.unop).inv ≫ SSet.opFunctor.map (g ≫ f) =
    ((edgewiseWeightReverseIso n.unop).inv ≫ SSet.opFunctor.map g) ≫ SSet.opFunctor.map f
  rw [SSet.opFunctor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories
