module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientDGFunctor

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式から係数 dg 圏への関手性。
方針：包含上の標準 Hom 同定で恒等と合成を計算し、豊穣関手の外延性へ移す。
規約：図式の射の恒等・合成を実際の dg 関手の等式にする。
使われ方：例外因子の図式同型から指定逆を持つ係数 dg 関手を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G H : J ⥤ Mon (Complex R)}

/-- 概要：係数図式の恒等射は各 Hom 複体の恒等射を誘導する。
方針：包含の二つの同定を消去し、非包含では零複体の恒等同定を読む。
規約：KST §3.1。使われ方：係数 dg 関手の恒等保存。 -/
theorem diagramCoefficientHomMap_id (F : J ⥤ Mon (Complex R)) (i j : J) :
    diagramCoefficientHomMap (𝟙 F) i j = 𝟙 _ := by
  by_cases h : i ≤ j
  · simp only [diagramCoefficientHomMap, dite_eq_left h, NatTrans.id_app, Mon.id_hom',
      Category.id_comp, diagramModuleHomInclusion, eqToHom_trans, eqToHom_refl]
  · simp only [diagramCoefficientHomMap, dite_eq_right h, eqToHom_refl]

/-- 概要：係数図式の射の合成は Hom 写像の合成を誘導する。
方針：包含上で標準 Hom 同定を消去し、成分の合成を比較する。
規約：KST §3.1。使われ方：係数 dg 関手の合成保存。 -/
theorem diagramCoefficientHomMap_comp (α : F ⟶ G) (β : G ⟶ H) (i j : J) :
    diagramCoefficientHomMap α i j ≫ diagramCoefficientHomMap β i j =
      diagramCoefficientHomMap (α ≫ β) i j := by
  by_cases h : i ≤ j
  · let : IsIso (diagramModuleHomInclusion F h) := by
      unfold diagramModuleHomInclusion
      infer_instance
    apply (cancel_epi (diagramModuleHomInclusion F h)).mp
    rw [← Category.assoc, diagramCoefficientHomMap_inclusion, Category.assoc,
      diagramCoefficientHomMap_inclusion, diagramCoefficientHomMap_inclusion]
    rfl
  · simp only [diagramCoefficientHomMap, dite_eq_right h, eqToHom_trans]

/-- 概要：係数図式の恒等射の dg 関手は恒等。
方針：添字を保つ対象写像と Hom の恒等保存を外延性で束ねる。
規約：KST §3.1。使われ方：図式同型の逆の dg 関手法則。 -/
theorem diagramCoefficientDGFunctor_id (F : J ⥤ Mon (Complex R)) :
    diagramCoefficientDGFunctor (𝟙 F) = DGFunctor.id (DiagramModuleCoefficientObject F) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact diagramCoefficientHomMap_id F x.index y.index

/-- 概要：係数図式の射の合成と係数 dg 関手の合成は一致する。
方針：同じ対象の添字と Hom の合成保存を使う。
規約：KST §3.1・Lemma 3.6。使われ方：指定逆と係数表示変更の整合性。 -/
theorem diagramCoefficientDGFunctor_comp (α : F ⟶ G) (β : G ⟶ H) :
    (diagramCoefficientDGFunctor α).comp (diagramCoefficientDGFunctor β) =
      diagramCoefficientDGFunctor (α ≫ β) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact diagramCoefficientHomMap_comp α β x.index y.index

/-- 概要：図式同型の順方向と逆方向の係数 dg 関手の合成は恒等。
方針：係数 dg 関手の合成保存と図式同型の逆条件を使う。
規約：KST Lemma 3.6。使われ方：係数表示を変更する指定逆。 -/
theorem diagramCoefficientDGFunctor_hom_inv (e : F ≅ G) :
    (diagramCoefficientDGFunctor e.hom).comp (diagramCoefficientDGFunctor e.inv) =
      DGFunctor.id (DiagramModuleCoefficientObject F) := by
  rw [diagramCoefficientDGFunctor_comp, e.hom_inv_id, diagramCoefficientDGFunctor_id]

/-- 概要：図式同型の逆方向と順方向の係数 dg 関手の合成も恒等。
方針：逆向きの同型の逆条件を同じ合成則へ適用する。
規約：KST Lemma 3.6。使われ方：指定係数 dg 比較の両側逆。 -/
theorem diagramCoefficientDGFunctor_inv_hom (e : F ≅ G) :
    (diagramCoefficientDGFunctor e.inv).comp (diagramCoefficientDGFunctor e.hom) =
      DGFunctor.id (DiagramModuleCoefficientObject G) := by
  rw [diagramCoefficientDGFunctor_comp, e.inv_hom_id, diagramCoefficientDGFunctor_id]

end SerrePositivity.KST.DerivedBlowup
