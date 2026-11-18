module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension

/-!
概要：図式等式を伴う錐の制限と頂点射影。
方針：元のスライス関手の全次数の射影等式をホモトピー圏で評価する。
  文献対応：HTT 1.2.13、Kerodon §7.1（Tag 02H1）の固定図式の制限。
使われ方：形状を変える指定極限比較の辺を同じ頂点上にそろえる。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {A B X : SSet.{u}} {p : A ⟶ X} {q : B ⟶ X}

/-- 図式の等式を伴う同じスライス制限。 -/
def sliceRestrictAlong (f : A ⟶ B) (h : f ≫ q = p) : sliceOver q ⟶ sliceOver p :=
  sliceOverRestrict q f ≫ eqToHom (congrArg sliceOver h)

/-- 図式の等式を伴う制限は同じ図式の錐を与える。 -/
lemma sliceRestrictAlong_cone (f : A ⟶ B) (h : f ≫ q = p) (d : JoinCone q) :
    (sliceRestrictAlong f h).app (Opposite.op ⦋0⦌) d = (restrictJoinCone d f).cast h := by
  subst p
  unfold sliceRestrictAlong
  rw [eqToHom_refl, Category.comp_id]
  rfl

private lemma sliceOver_cast_val_all {K : SSet.{u}} {r s : K ⟶ X} (h : r = s)
    (n : SimplexCategoryᵒᵖ) (a : (sliceOver r).obj n) :
    ((eqToHom (congrArg sliceOver h)).app n a).val = a.val := by
  subst s
  rfl

/-- 図式等式をそろえて二回制限することは、同じ添字射の合成に沿う制限になる。 -/
lemma sliceRestrictAlong_comp {D : SSet.{u}} {r : D ⟶ X}
    (f : A ⟶ B) (g : B ⟶ D) (hf : f ≫ q = p) (hg : g ≫ r = q)
    (h : (f ≫ g) ≫ r = p) :
    sliceRestrictAlong g hg ≫ sliceRestrictAlong f hf = sliceRestrictAlong (f ≫ g) h := by
  subst q
  subst p
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToHom (congrArg sliceOver hf)).app n
      ((sliceOverRestrict (g ≫ r) f).app n ((sliceOverRestrict r g).app n s))).val = _
  rw [sliceOver_cast_val_all hf]
  simp only [sliceRestrictAlong, eqToHom_refl, Category.comp_id]
  change joinMap (𝟙 _) f ≫ (joinMap (𝟙 _) g ≫ s.val) =
    joinMap (𝟙 _) (f ≫ g) ≫ s.val
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp]

/-- 図式の等式を伴う制限も元の頂点射影を保つ。 -/
lemma sliceRestrictAlong_projection (f : A ⟶ B) (h : f ≫ q = p) :
    sliceRestrictAlong f h ≫ sliceOverProjection p = sliceOverProjection q := by
  rw [sliceRestrictAlong, Category.assoc]
  exact (congrArg (fun k => sliceOverRestrict q f ≫ k) (sliceOverProjection_eqTransport h)).trans
    (sliceOverRestrict_projection q f)

/-- 制限に伴う錐の頂点の等式を使用して、同じ射の頂点射影を回収する。 -/
@[cite HTT "1.2.13" (partial := special) "図式の制限における頂点射影の自然性。"]
lemma sliceRestrictAlong_hom_projection (f : A ⟶ B) (h : f ≫ q = p)
    (d e : JoinCone q)
    (α : (HomotopyCategory.mk d : hoFunctor.obj (sliceOver q)) ⟶ HomotopyCategory.mk e) :
    let G := (hoFunctor.map (sliceRestrictAlong f h)).toFunctor
    let π := (hoFunctor.map (sliceOverProjection p)).toFunctor
    let ψ := (hoFunctor.map (sliceOverProjection q)).toFunctor
    ∀ (hd : (π.obj (G.obj (HomotopyCategory.mk d))) = ψ.obj (HomotopyCategory.mk d))
      (he : (π.obj (G.obj (HomotopyCategory.mk e))) = ψ.obj (HomotopyCategory.mk e)),
    eqToHom hd.symm ≫ π.map (G.map α) ≫ eqToHom he = ψ.map α := by
  intro G π ψ hd he
  have hp : G ⋙ π = ψ := by
    change (hoFunctor.map (sliceRestrictAlong f h)).toFunctor ⋙ _ = _
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp, sliceRestrictAlong_projection]
  have hx : π.map (G.map α) ≫ eqToHom he = eqToHom hd ≫ ψ.map α := by
    simpa only [eqToHom_app, Functor.comp_map] using (eqToHom hp).naturality α
  calc
    _ = eqToHom hd.symm ≫ (π.map (G.map α) ≫ eqToHom he) := rfl
    _ = eqToHom hd.symm ≫ (eqToHom hd ≫ ψ.map α) := congrArg _ hx
    _ = _ := by rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
