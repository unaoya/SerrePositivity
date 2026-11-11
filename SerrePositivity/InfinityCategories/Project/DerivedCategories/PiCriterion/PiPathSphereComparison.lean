module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.SphereClassPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PathFamilyHomotopy
public import SerrePositivity.KST.Spectra.SphereMappingComponents
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-!
概要：実際の path による類の比較を、球面からの自由なホモトピーへ渡す。
方針：path 空間の一つの類を球面で表し、両端で指定代表と基点固定で比較する。
規約：両端の代表の基点は保持し、得られるホモトピーは基点を動かしてよい。
使われ方：基点移送の合成と D の全射性の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- 同じ点つき球面の類を持つ指定代表は、基点を忘れてもホモトピック。 -/
lemma sphereClass_eq_free_homotopy (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (f g : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n f = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n g) : Nonempty (Homotopy f.right g.right) := by
  have hc := (SphereSimplex.class_eq_iff_components Y n f g).mp h
  obtain ⟨H, _⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy f g).mp hc
  exact ⟨H⟩

/-- path 上で対応する二つの指定球面代表は、基点を動かすホモトピーを持つ。 -/
lemma piPathRelated_sphere_free_homotopy
    {X : SSet.{u}} [KanComplex X] (n : ℕ) (x y : X _⦋0⦌)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X x)
    (g : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X y)
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated (X := X) n
      (x := (PointedSimplicialSet.ofVertex X x).basepoint)
      (y := (PointedSimplicialSet.ofVertex X y).basepoint)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass (X := PointedSimplicialSet.ofVertex X x) n f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass (X := PointedSimplicialSet.ofVertex X y) n g)) :
    Nonempty (Homotopy f.right g.right) := by
  let Y := PointedSimplicialSet.ofVertex X x
  let Z := PointedSimplicialSet.ofVertex X y
  obtain ⟨z, h₀, h₁, γ, ha, hb⟩ := h
  let P := PointedSimplicialSet.ofVertex (KanPath.object Y.right) z
  let hp := PointedSimplicialSet.basepoint_ofVertex (KanPath.object Y.right) z
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl (KanPath.object Y.right)) hp
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_surjective P n (e.symm γ)
  have htγ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 (KanPath.object Y.right)) hp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n t) = γ := by
    change e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n t) = γ
    rw [ht, e.apply_symm_apply]
  let e₀ : P ⟶ Y := Under.homMk (KanPath.evaluation Y.right 0) (by
    apply (SSet.unitHomEquiv _).injective
    change (KanPath.evaluation Y.right 0).app _ P.basepoint = Y.basepoint
    exact (congrArg ((KanPath.evaluation Y.right 0).app _) hp).trans h₀)
  let e₁ : P ⟶ Z := Under.homMk (KanPath.evaluation Y.right 1) (by
    apply (SSet.unitHomEquiv _).injective
    change (KanPath.evaluation Y.right 1).app _ P.basepoint = Z.basepoint
    exact (congrArg ((KanPath.evaluation Y.right 1).app _) hp).trans h₁)
  have he₀ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n (t ≫ e₀) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n f := by
    have hs := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (𝟙 (KanPath.object Y.right)) (𝟙 Y.right)
      (KanPath.evaluation Y.right 0) (KanPath.evaluation Y.right 0) (by simp)
      hp rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e₀) h₀ n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n t)
    simp only [htγ, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id] at hs
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_post n t e₀).symm.trans (hs.symm.trans ha)
  have he₁ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n (t ≫ e₁) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n g := by
    have hs := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square (𝟙 (KanPath.object Y.right)) (𝟙 Y.right)
      (KanPath.evaluation Y.right 1) (KanPath.evaluation Y.right 1) (by simp)
      hp rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e₁) h₁ n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n t)
    simp only [htγ, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id] at hs
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_post n t e₁).symm.trans (hs.symm.trans hb)
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    (sphereClass_eq_free_homotopy Y n (t ≫ e₀) f he₀)
  have hg := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    (sphereClass_eq_free_homotopy Z n (t ≫ e₁) g he₁)
  have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.pathFamilyHomotopy t.right⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  simpa only [Category.comp_id] using hf.symm.trans (hm.trans hg)

/-- 指定した二つの球面代表に対し、実際の path 比較と自由ホモトピーは同値。 -/
lemma piPathRelated_sphere_iff_free_homotopy
    {X : SSet.{u}} [KanComplex X] (n : ℕ) (x y : X _⦋0⦌)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X x)
    (g : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated (X := X) n
        (x := (PointedSimplicialSet.ofVertex X x).basepoint)
        (y := (PointedSimplicialSet.ofVertex X y).basepoint)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass (X := PointedSimplicialSet.ofVertex X x) n f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass (X := PointedSimplicialSet.ofVertex X y) n g) ↔
      Nonempty (Homotopy f.right g.right) := by
  constructor
  · exact piPathRelated_sphere_free_homotopy n x y f g
  · rintro ⟨H⟩
    obtain ⟨z, h₀, h₁, γ, ha, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_path_witness n x y f g H
    exact ⟨z, h₀, h₁, γ, ha, hb⟩

private lemma groupMap_id_rebase_cancel {X : SSet.{u}} [KanComplex X] (n : ℕ)
    {x y : X _⦋0⦌} (h : x = y) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) h.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) h a) = a := by
  subst y
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id, MonoidHom.id_apply]

/-- 任意の元の基点の類を、同じ頂点を指定した球面射で表す。 -/
lemma vertex_sphere_representative {X : SSet.{u}} [KanComplex X] (n : ℕ)
    (x : X _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    ∃ f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X x,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) (PointedSimplicialSet.basepoint_ofVertex X x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n f) = a := by
  let hx := PointedSimplicialSet.basepoint_ofVertex X x
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_surjective (PointedSimplicialSet.ofVertex X x) n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) hx.symm a)
  refine ⟨f, ?_⟩
  rw [hf]
  exact groupMap_id_rebase_cancel n hx.symm a

/-- 元の基点に戻した球面代表を固定すると、path 比較はその自由ホモトピーと同値。 -/
lemma piPathRelated_iff_representative_homotopy {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (x y : X _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X x)
    (g : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) (PointedSimplicialSet.basepoint_ofVertex X x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n f) = a)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) (PointedSimplicialSet.basepoint_ofVertex X y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n g) = b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n a b ↔ Nonempty (Homotopy f.right g.right) := by
  let hx := PointedSimplicialSet.basepoint_ofVertex X x
  let hy := PointedSimplicialSet.basepoint_ofVertex X y
  constructor
  · intro hab
    have hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) hx.symm a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n f := by
      rw [← hf]
      exact groupMap_id_rebase_cancel n hx _
    have hg' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) hy.symm b = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n g := by
      rw [← hg]
      exact groupMap_id_rebase_cancel n hy _
    have hfg := hab.rebase hx.symm hy.symm
    rw [hf', hg'] at hfg
    exact (piPathRelated_sphere_iff_free_homotopy n x y f g).mp hfg
  · intro H
    have hab := ((piPathRelated_sphere_iff_free_homotopy n x y f g).mpr H).rebase hx hy
    exact (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n a b) hf hg).mp hab

/-- 実際の path による類の比較を合成できる。閉路の作用は等式として潰さない。 -/
lemma PiPathRelated.trans {X : SSet.{u}} [KanComplex X] {n : ℕ}
    {x y z : X _⦋0⦌} {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x}
    {b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n z}
    (hab : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n a b) (hbc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n b c) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n a c := by
  obtain ⟨f, hf⟩ := vertex_sphere_representative n x a
  obtain ⟨g, hg⟩ := vertex_sphere_representative n y b
  obtain ⟨h, hh⟩ := vertex_sphere_representative n z c
  have Hfg := (piPathRelated_iff_representative_homotopy n x y a b f g hf hg).mp hab
  have Hgh := (piPathRelated_iff_representative_homotopy n y z b c g h hg hh).mp hbc
  apply (piPathRelated_iff_representative_homotopy n x z a c f h hf hh).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr Hfg).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr Hgh))

/-- 同じ基点経路を逆向きの自由ホモトピーで戻した比較が存在する。 -/
lemma PiPathRelated.symm {X : SSet.{u}} [KanComplex X] {n : ℕ}
    {x y : X _⦋0⦌} {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (hab : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n a b) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n b a := by
  obtain ⟨f, hf⟩ := vertex_sphere_representative n x a
  obtain ⟨g, hg⟩ := vertex_sphere_representative n y b
  have H := (piPathRelated_iff_representative_homotopy n x y a b f g hf hg).mp hab
  apply (piPathRelated_iff_representative_homotopy n y x b a g f hg hf).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr H).symm

/-- 元の射のホモトピーは、任意の類の両像を実際の基点経路で比較する。 -/
lemma piPathRelated_of_homotopy {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f g : X ⟶ Y} (H : Homotopy f g) (n : ℕ) (x : X _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g rfl a) := by
  let t := KanPath.transpose H
  let z := t.app (Opposite.op ⦋0⦌) x
  have h₀ : (KanPath.evaluation Y 0).app _ z = f.app _ x :=
    congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) x) (KanPath.transpose_zero H)
  have h₁ : (KanPath.evaluation Y 1).app _ z = g.app _ x :=
    congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) x) (KanPath.transpose_one H)
  refine ⟨z, h₀, h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map t rfl a, ?_, ?_⟩
  · have hs := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square t (𝟙 Y) f (KanPath.evaluation Y 0)
      (by simpa only [t, Category.comp_id] using KanPath.transpose_zero H) rfl rfl rfl h₀ n a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id] at hs
    exact hs
  · have hs := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square t (𝟙 Y) g (KanPath.evaluation Y 1)
      (by simpa only [t, Category.comp_id] using KanPath.transpose_one H) rfl rfl rfl h₁ n a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id] at hs
    exact hs

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
