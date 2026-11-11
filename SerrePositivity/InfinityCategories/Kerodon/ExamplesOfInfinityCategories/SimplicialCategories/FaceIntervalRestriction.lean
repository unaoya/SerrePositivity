module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.IntervalChoice

/-!
# 真部分区間の Hom 回収の既知面への制限

概要：真部分区間の標準回収と元のホーンの既知面の回収を比較する。
方針：面内の射影で二つの既知面を比較し、区間の Hom 同型で周囲へ移す。
規約：追加の整合性仮定や局所 Kan 性は用いない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の零座標面と合成面の貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {J : Type v} [LinearOrder J]
/-- 概要：等しい順序写像に沿う既知面の回収豊穣関手は等しい。
方針：順序写像の等式で置換し、除外の証明の一意性を使う。
規約：Mathlib の native な Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma hornFunctorViaFace_congr {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i)
    (f g : J →o ULift.{v} (Fin (n + 3))) (h : f = g)
    (hf : ∀ x, (f x).down ≠ j) (hg : ∀ x, (g x).down ≠ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj f hf = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj g hg := by
  subst g
  rfl
/-- 概要：既知面をその面への埋め込みに沿って回収した豊穣関手は元の面の回収に等しい。
方針：面と退化の合成が恒等射であることを共通対象への移送へ適用する。
規約：Mathlib の native な Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma hornFunctorViaFace_on_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj (SimplexCategory.δ j).toOrderHom.uliftMap
      (fun x ↦ Fin.succAbove_ne j x.down) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorOnCell σ (SSet.horn.face i j hj) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorOnCell
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor_congr
  change (SimplicialNerve C).map (SimplexCategory.δ j).op
      ((SimplicialNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).op (σ.app _ (SSet.horn.face i j hj))) = _
  rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_section,
    op_id, CategoryTheory.Functor.map_id]
  rfl

/-- 概要：既知面内の閉区間上で、その面と区間外の別の面からの回収は等しい。
方針：面内の射影と面への埋め込みを合成した同じ単体上で比較し、区間へ制限する。
規約：Mathlib の native な Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma hornFunctorViaFace_face_interval_eq {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (a b : Fin (n + 2)) (hab : a ≤ b) (hout : k < j.succAbove a ∨ j.succAbove b < k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ j hj
      ((SimplexCategory.δ j).toOrderHom.uliftMap.comp
        (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o _))
      (fun x ↦ Fin.succAbove_ne j x.val.down) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ k hk
      ((SimplexCategory.δ j).toOrderHom.uliftMap.comp
        (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o _))
      (fun x h ↦ by
        have hx := x.property
        change a ≤ x.val.down ∧ x.val.down ≤ b at hx
        rcases hout with hka | hbk
        · exact (ne_of_gt (lt_of_lt_of_le hka ((Fin.strictMono_succAbove j).monotone hx.1))) h
        · exact (ne_of_lt (lt_of_le_of_lt
          ((Fin.strictMono_succAbove j).monotone hx.2) hbk)) h) := by
  let e : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) →o ULift.{v} (Fin (n + 2)) :=
    ⟨Subtype.val, fun _ _ h ↦ h⟩
  let d := (SimplexCategory.δ j).toOrderHom.uliftMap
  let θ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClampSimplex a b ≫ SimplexCategory.δ j
  have hjθ : ∀ x, θ.toOrderHom x ≠ j := fun x ↦ Fin.succAbove_ne j _
  have hkθ : ∀ x, θ.toOrderHom x ≠ k := by
    intro x
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClamp_mem a b hab x
    rcases hout with hka | hbk
    · exact ne_of_gt (lt_of_lt_of_le hka ((Fin.strictMono_succAbove j).monotone hx.1))
    · exact ne_of_lt (lt_of_le_of_lt ((Fin.strictMono_succAbove j).monotone hx.2) hbk)
  have he : θ.toOrderHom.uliftMap.comp e = d.comp e := by
    apply OrderHom.ext
    funext x
    apply ULift.ext
    change j.succAbove (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClamp a b x.val.down) = j.succAbove x.val.down
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalClamp_fixed a b x.val.down x.property]
  have hr (t : Fin (n + 3)) (ht : t ≠ i) (hθ : ∀ x, θ.toOrderHom x ≠ t)
      (hf : ∀ x, ((d.comp e) x).down ≠ t) :
      (SimplicialThickening.functor e).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ t ht θ.toOrderHom.uliftMap (fun x ↦ hθ x.down)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace σ t ht (d.comp e) hf :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_comp σ t ht θ.toOrderHom.uliftMap (fun x ↦ hθ x.down) e).trans
      (hornFunctorViaFace_congr σ t ht _ _ he _ _)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_simplex_eq σ θ j k hj hk hjθ hkθ
  exact (hr j hj hjθ _).symm.trans
    ((congrArg (fun F ↦ (SimplicialThickening.functor e).comp SSet F) h).trans (hr k hk hkθ _))
/-- 概要：区間外の点は両端点と異なる。
方針：区間の順序と外側の不等式を合成する。
規約：Mathlib の native な Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma outsideInterval_ne_ends {a b j : J} (hab : a ≤ b) (hout : j < a ∨ b < j) :
    a ≠ j ∧ b ≠ j := by
  rcases hout with h | h
  · exact ⟨ne_of_gt h, ne_of_gt (lt_of_lt_of_le h hab)⟩
  · exact ⟨ne_of_lt (lt_of_le_of_lt hab h), ne_of_lt h⟩

set_option backward.isDefEq.respectTransparency false in
/-- 概要：別の面の区間外候補を元の面の Hom へ制限すると元の回収に等しい。
方針：面内区間の豊穣関手の等式を両端で評価し、区間の Hom 同型で前合成して比較する。
規約：Mathlib の native な Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma hornHomViaFace_on_face_of_outside {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (a b : Fin (n + 2)) (hab : a ≤ b) (hout : k < j.succAbove a ∨ j.succAbove b < k) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
      ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ k hk (j.succAbove a) (j.succAbove b)
        (outsideInterval_ne_ends ((Fin.strictMono_succAbove j).monotone hab) hout).1
        (outsideInterval_ne_ends ((Fin.strictMono_succAbove j).monotone hab) hout).2 =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face i j hj) a b := by
  let x : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) := ⟨ULift.up a, le_rfl, hab⟩
  let y : Set.Icc (ULift.up.{v} a) (ULift.up.{v} b) := ⟨ULift.up b, hab, le_rfl⟩
  have hm (F G : EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{v} a) (ULift.up.{v} b))) C) (h : F = G) :
      HEq (F.map (.mk x) (.mk y)) (G.map (.mk x) (.mk y)) := by
    subst G
    rfl
  have hh := hm _ _ (hornFunctorViaFace_face_interval_eq σ j k hj hk a b hab hout)
  have h := eq_of_heq hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFunctorViaFace_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningFunctor_comp_map] at h
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso x y).hom).mp
  have h' : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso x y).hom ≫
      ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
        ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (j.succAbove a) (j.succAbove b)
          (Fin.succAbove_ne j a) (Fin.succAbove_ne j b)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalPathHomIso x y).hom ≫
      ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
        ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ k hk (j.succAbove a) (j.succAbove b)
          (outsideInterval_ne_ends ((Fin.strictMono_succAbove j).monotone hab) hout).1
          (outsideInterval_ne_ends ((Fin.strictMono_succAbove j).monotone hab) hout).2) := by
    convert h using 1 <;> rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face] at h'
  exact h'.symm
/-- 概要：標準の真部分区間 Hom を任意の既知面へ制限するとその面の Hom 回収に等しい。
方針：区間外の端の面を選び、選択独立性と面内区間の比較を使う。
規約：Mathlib の native な Path Hom と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma hornProperIntervalHom_on_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 2)) (hab : a ≤ b)
    (hp : j.succAbove a ≠ 0 ∨ j.succAbove b ≠ Fin.last (n + 2)) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
      ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn (j.succAbove a) (j.succAbove b)
        ((Fin.strictMono_succAbove j).monotone hab) hp =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face i j hj) a b := by
  have go (k : Fin (n + 3)) (hk : k ≠ i)
      (hout : k < j.succAbove a ∨ j.succAbove b < k) :
      (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
        ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn (j.succAbove a) (j.succAbove b)
          ((Fin.strictMono_succAbove j).monotone hab) hp =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face i j hj) a b := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom_eq_viaFace σ h0 hn (j.succAbove a) (j.succAbove b)
      ((Fin.strictMono_succAbove j).monotone hab) hp k hk hout]
    exact hornHomViaFace_on_face_of_outside σ j k hj hk a b hab hout
  by_cases ha : j.succAbove a = 0
  · exact go (Fin.last (n + 2)) (ne_of_gt hn)
      (Or.inr (lt_of_le_of_ne (Fin.le_last _) (hp.resolve_left (fun h ↦ h ha))))
  · exact go 0 (ne_of_lt h0) (Or.inl (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha)))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
