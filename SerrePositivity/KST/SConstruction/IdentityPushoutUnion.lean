module
public import SerrePositivity.KST.SConstruction.IdentityPushoutOverlap

/-! # 二つの恒等 span の部分複体の貼り合わせ
概要：どちらかの枝が恒等である span の全ての族に標準押し出しを同時に与える。
方針：二つの像の和で復元を貼り合わせ、重なりの厳密な一致を使う。
規約：頂点だけでなく全単体で貼る。使われ方：McCarthy 法の両側の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
attribute [local instance] Classical.propDecidable

/-- 概要：二つの部分複体で一致する二つの射を、その和で貼り合わせる。
方針：片側への所属で場合分けし、共通部分での一致から自然性を示す。
規約：射は周囲の単体集合上で与える。使われ方：恒等 span の標準四角形の同時の復元。 -/
def subcomplexUnionMap {X Y : SSet.{u}} (S T : X.Subcomplex) (f g : X ⟶ Y)
    (h : ∀ n v, v ∈ S.obj n → v ∈ T.obj n → f.app n v = g.app n v) :
    ((S ⊔ T : X.Subcomplex) : SSet.{u}) ⟶ Y where
  app n := ↾fun v => if v.val ∈ S.obj n then f.app n v.val else g.app n v.val
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro v
    have hf := ConcreteCategory.congr_hom (f.naturality α) v.val
    have hg := ConcreteCategory.congr_hom (g.naturality α) v.val
    change f.app m (X.map α v.val) = Y.map α (f.app n v.val) at hf
    change g.app m (X.map α v.val) = Y.map α (g.app n v.val) at hg
    change (if X.map α v.val ∈ S.obj m then f.app m (X.map α v.val)
        else g.app m (X.map α v.val)) =
      Y.map α (if v.val ∈ S.obj n then f.app n v.val else g.app n v.val)
    by_cases hn : v.val ∈ S.obj n
    · have hm : X.map α v.val ∈ S.obj m := S.map α hn
      rw [ite_eq_left hn, ite_eq_left hm]
      exact hf
    · have ht : v.val ∈ T.obj n := v.property.resolve_left hn
      have htm := T.map α ht
      by_cases hm : X.map α v.val ∈ S.obj m
      · simpa only [ite_eq_right hn, ite_eq_left hm] using (h m _ hm htm).trans hg
      · simpa only [ite_eq_right hn, ite_eq_right hm] using hg

private lemma subcomplexUnionMap_left {X Y : SSet.{u}} (S T : X.Subcomplex) (f g : X ⟶ Y)
    (h : ∀ n v, v ∈ S.obj n → v ∈ T.obj n → f.app n v = g.app n v)
    (n) (v : (S ⊔ T : X.Subcomplex).obj n) (hv : v.val ∈ S.obj n) :
    (subcomplexUnionMap S T f g h).app n v = f.app n v.val := ite_eq_left hv

private lemma subcomplexUnionMap_right {X Y : SSet.{u}} (S T : X.Subcomplex) (f g : X ⟶ Y)
    (h : ∀ n v, v ∈ S.obj n → v ∈ T.obj n → f.app n v = g.app n v)
    (n) (v : (S ⊔ T : X.Subcomplex).obj n) (hv : v.val ∈ T.obj n) :
    (subcomplexUnionMap S T f g h).app n v = g.app n v.val := by
  by_cases hs : v.val ∈ S.obj n
  · exact (ite_eq_left hs).trans (h n _ hs hv)
  · exact ite_eq_right hs

/-- 概要：どちらかの枝が恒等である span の単体的な部分複体。
方針：二つの標準 span の族の像の和を取る。
規約：全ての高次の族を保持する。使われ方：両向きの同時正規化の入力。 -/
def identitySpanSubcomplex (C : SSet.{u}) : ((ihom (horn 2 0 : SSet.{u})).obj C).Subcomplex :=
  Subcomplex.range (identitySpanFamily false C) ⊔ Subcomplex.range (identitySpanFamily true C)

/-- 概要：どちらかの枝が恒等である span の標準四角形の同時の復元。
方針：二つの復元を像の和で貼り合わせる。
規約：重なりでは厳密に一致する。使われ方：押し出しの族への持ち上げ。 -/
def identityUnionSquare (C : SSet.{u}) :
    (identitySpanSubcomplex C : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  subcomplexUnionMap _ _ (identitySquareReconstruction false C)
    (identitySquareReconstruction true C)
    (identitySquareReconstruction_overlap C)

private lemma comp_apply_eq {A B D : SSet.{u}} (f : A ⟶ B) (g : B ⟶ D) (k : A ⟶ D)
    (h : f ≫ g = k) (n : SimplexCategoryᵒᵖ) (v : A.obj n) :
    g.app n (f.app n v) = k.app n v :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h n) v

/-- 概要：和の上の復元は各標準 span で指定の退化四角形を回収する。
方針：和の貼り合わせの各側の式と、標準 span の復元の式を使う。
規約：任意の次数の族についての式。使われ方：標準四角形の押し出し性。 -/
lemma identityUnionSquare_on_family (C : SSet.{u}) (b : Bool) (n : SimplexCategoryᵒᵖ)
    (g : ((ihom (Δ[1] : SSet.{u})).obj C).obj n)
    (v : (identitySpanSubcomplex C).obj n) (hv : v.val = (identitySpanFamily b C).app n g) :
    (identityUnionSquare C).app n v = ((pre (identityPushoutShape b)).app C).app n g := by
  have h : (identityUnionSquare C).app n v = (identitySquareReconstruction b C).app n v.val := by
    cases b with
    | false => exact subcomplexUnionMap_left _ _ _ _ _ n v (by rw [hv]; exact ⟨g, rfl⟩)
    | true => exact subcomplexUnionMap_right _ _ _ _ _ n v (by rw [hv]; exact ⟨g, rfl⟩)
  rw [h, hv]
  exact comp_apply_eq _ _ _ (identitySpanFamily_reconstruction b C) n g

/-- 概要：和の上の標準四角形は元の入力 span を厳密に回収する。
方針：各像の元に分け、前合成の合成則を適用する。
規約：部分複体の包含そのもの。使われ方：相対切断の可換条件。 -/
lemma identityUnionSquare_span (C : SSet.{u}) :
    identityUnionSquare C ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = (identitySpanSubcomplex C).ι := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  have hv : ∃ b g, v.val = (identitySpanFamily b C).app n g := by
    rcases v.property with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact ⟨false, g, hg.symm⟩
    · exact ⟨true, g, hg.symm⟩
  obtain ⟨b, g, hg⟩ := hv
  change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C).app n ((identityUnionSquare C).app n v) = v.val
  rw [identityUnionSquare_on_family C b n g v hg, hg]
  exact comp_apply_eq _ _ _ (show
    (pre (identityPushoutShape b)).app C ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C =
      identitySpanFamily b C by rw [← NatTrans.comp_app, ← pre_map]; rfl) n g

/-- 概要：どちらかの枝が恒等である span の全ての族の標準押し出し。
方針：和の上の復元の頂点を各像に分け、標準四角形の押し出し性を使う。
規約：両向きの条件を同時に満たす。使われ方：関手的な押し出しの同時正規化。 -/
def identityUnionPushoutFamily (C : SSet.{u}) [Quasicategory C] :
    (identitySpanSubcomplex C : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex (identityUnionSquare C) (by
    intro v
    have hv : ∃ b g, v.val = (identitySpanFamily b C).app (Opposite.op ⦋0⦌) g := by
      rcases v.property with ⟨g, hg⟩ | ⟨g, hg⟩
      · exact ⟨false, g, hg.symm⟩
      · exact ⟨true, g, hg.symm⟩
    obtain ⟨b, g, hg⟩ := hv
    obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) C).surjective g
    rw [identityUnionSquare_on_family C b (Opposite.op ⦋0⦌) _ v hg]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (identityPushoutShape b ≫ G)))
    rw [Equiv.symm_apply_apply]
    exact identityPushoutShape_isPushout b G)

/-- 概要：同時に正規化した押し出し族は部分複体の入力を回収する。
方針：全部分複体の包含と和の復元の式。
規約：全単体での厳密等号。使われ方：全 span への正規化付きの切断の延長。 -/
lemma identityUnionPushoutFamily_projection (C : SSet.{u}) [Quasicategory C] :
    identityUnionPushoutFamily C ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C = (identitySpanSubcomplex C).ι := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection, ← Category.assoc]
  exact identityUnionSquare_span C

end SerrePositivity.KST.SConstruction
