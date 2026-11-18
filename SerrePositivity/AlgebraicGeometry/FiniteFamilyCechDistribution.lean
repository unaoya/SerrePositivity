module

public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCechUnit
public import Mathlib.CategoryTheory.Extensive

/-!
概要：同じ有限余積とファイバー冪の標準比較は全次数で同型。
方針：混合ファイバー積の Cartesian な帰納と既存の有限余積の分配を使う。
規約：各入射と射影で、同じ標準射そのものの同型性を示す。
使われ方：元の有限アフィン族の nerve と矩形タプルの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {ι : Type} {S : Scheme.{u}} {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ S)

/-- 同じ標準射は、元の各混合ファイバー積の基底への射を保つ。 -/
theorem finiteFamilyCechMap_base (n : SimplexCategory) :
    finiteFamilyCechMap f n ≫
        WidePullback.base (fun _ : Fin (n.len + 1) ↦ Sigma.desc f) =
      Sigma.desc (fun t : Fin (n.len + 1) → ι ↦ WidePullback.base (fun j ↦ f (t j))) := by
  apply Sigma.hom_ext
  intro t
  rw [finiteFamilyCechMap, ← Category.assoc, Sigma.ι_comp_desc,
    finiteFamilyCechInclusion_base, Sigma.ι_comp_desc]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ有限余積の標準比較の同型性は、元の Cartesian square により後続次数へ進む。 -/
theorem finiteFamilyCechMap_succ_isIso [Finite ι] (n : ℕ)
    [IsIso (finiteFamilyCechMap f (SimplexCategory.mk n))] :
    IsIso (finiteFamilyCechMap f (SimplexCategory.mk (n + 1))) := by
  let T := Fin (n + 1) → ι
  let V (t : T) := finiteFamilyCechComponent f (SimplexCategory.mk n) t
  let b (t : T) : V t ⟶ S := WidePullback.base (fun j ↦ f (t j))
  let B := Sigma.desc b
  let F := finiteFamilyCechMap f (SimplexCategory.mk n)
  let c := WidePullback.base (fun _ : Fin (n + 1) ↦ Sigma.desc f)
  have hF : F ≫ c = B := finiteFamilyCechMap_base f (SimplexCategory.mk n)
  let R (p : T × ι) := pullback (b p.1) (f p.2)
  let e : (Fin (n + 2) → ι) ≃ T × ι :=
    { toFun := fun t ↦ (fun j ↦ t j.succ, t 0)
      invFun := fun p ↦ Fin.cases p.2 p.1
      left_inv := fun t ↦ funext (fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j)
      right_inv := fun p ↦ by cases p; rfl }
  let et (t : Fin (n + 2) → ι) :
      finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t ≅ R (e t) :=
    (isPullback_finiteFamilyFiberSucc n (fun j ↦ f (t j))).isoPullback
  let dm (p : T × ι) : R p ⟶ pullback B (Sigma.desc f) :=
    pullback.map (b p.1) (f p.2) B (Sigma.desc f) (Sigma.ι V p.1) (Sigma.ι Z p.2)
      (𝟙 S) (by simp only [B, Sigma.ι_comp_desc, Category.comp_id])
      (by simp only [Sigma.ι_comp_desc, Category.comp_id])
  let d := Sigma.desc dm
  haveI : IsIso d := by
    dsimp only [d, dm, B]
    infer_instance
  let D : pullback B (Sigma.desc f) ⟶ pullback c (Sigma.desc f) :=
    pullback.map B (Sigma.desc f) c (Sigma.desc f) F (𝟙 _) (𝟙 S)
      (by simpa only [Category.comp_id] using hF.symm) (by simp)
  haveI : IsIso F := inferInstance
  haveI : IsIso D := by dsimp only [D]; infer_instance
  let H := isPullback_finiteFiberPowerSucc (Sigma.desc f) n
  let E := CategoryTheory.Limits.Sigma.mapIso et ≪≫
    CategoryTheory.Limits.Sigma.reindex e R ≪≫ asIso d ≪≫ asIso D ≪≫ H.isoPullback.symm
  let tail := WidePullback.lift
    (WidePullback.base (fun _ : Fin (n + 2) ↦ Sigma.desc f))
    (fun j : Fin (n + 1) ↦ WidePullback.π
      (fun _ : Fin (n + 2) ↦ Sigma.desc f) j.succ)
    (fun j ↦ WidePullback.π_arrow (fun _ : Fin (n + 2) ↦ Sigma.desc f) j.succ)
  let mt (t : Fin (n + 2) → ι) := WidePullback.lift (WidePullback.base (fun j ↦ f (t j)))
    (fun j : Fin (n + 1) ↦ WidePullback.π (fun j ↦ f (t j)) j.succ)
    (fun j ↦ WidePullback.π_arrow (fun j ↦ f (t j)) j.succ)
  have hE (t : Fin (n + 2) → ι) :
      Sigma.ι (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          E.hom ≫ H.isoPullback.hom = (et t).hom ≫ dm (e t) ≫ D := by
    simp only [E, Iso.trans_hom, Category.assoc, Iso.symm_hom, asIso_hom,
      Iso.inv_hom_id, Category.comp_id, Sigma.ι_mapIso_hom_assoc]
    have hr := Sigma.ι_reindex_hom e R t
    change Sigma.ι (fun t ↦ R (e t)) t ≫
      (CategoryTheory.Limits.Sigma.reindex e R).hom = Sigma.ι R (e t) at hr
    have hc := congrArg (fun k ↦ (et t).hom ≫ k ≫ d ≫ D) hr
    simpa only [Category.assoc, d, Sigma.ι_comp_desc_assoc] using hc
  have hhead (t : Fin (n + 2) → ι) :
      Sigma.ι (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          E.hom ≫ WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) 0 =
        WidePullback.π (fun j ↦ f (t j)) 0 ≫ Sigma.ι Z (t 0) := by
    have hN : H.isoPullback.hom ≫ pullback.snd c (Sigma.desc f) =
        WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) 0 :=
      H.isoPullback_hom_snd
    have hk := congrArg (fun k ↦ k ≫ pullback.snd c (Sigma.desc f)) (hE t)
    have hπ : Sigma.ι
          (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          E.hom ≫ WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) 0 =
        (et t).hom ≫ dm (e t) ≫ D ≫ pullback.snd c (Sigma.desc f) := by
      simpa only [Category.assoc, hN] using hk
    rw [hπ]
    simp only [D, dm, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
    change (et t).hom ≫ pullback.snd (b (fun j ↦ t j.succ)) (f (t 0)) ≫
      Sigma.ι Z (t 0) = _
    have hm : (et t).hom ≫ pullback.snd (b (fun j ↦ t j.succ)) (f (t 0)) =
        WidePullback.π (fun j ↦ f (t j)) 0 :=
      (isPullback_finiteFamilyFiberSucc n (fun j ↦ f (t j))).isoPullback_hom_snd
    rw [← Category.assoc, hm]
  have htail (t : Fin (n + 2) → ι) :
      Sigma.ι (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          E.hom ≫ tail = mt t ≫ finiteFamilyCechInclusion f (SimplexCategory.mk n)
            (fun j ↦ t j.succ) := by
    have hN : H.isoPullback.hom ≫ pullback.fst c (Sigma.desc f) = tail :=
      H.isoPullback_hom_fst
    have hk := congrArg (fun k ↦ k ≫ pullback.fst c (Sigma.desc f)) (hE t)
    have hπ : Sigma.ι
          (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          E.hom ≫ tail = (et t).hom ≫ dm (e t) ≫ D ≫ pullback.fst c (Sigma.desc f) := by
      simpa only [Category.assoc, hN] using hk
    rw [hπ]
    simp only [D, dm, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    change (et t).hom ≫ pullback.fst (b (fun j ↦ t j.succ)) (f (t 0)) ≫
      Sigma.ι V (fun j ↦ t j.succ) ≫ F = _
    have hm : (et t).hom ≫ pullback.fst (b (fun j ↦ t j.succ)) (f (t 0)) = mt t :=
      (isPullback_finiteFamilyFiberSucc n (fun j ↦ f (t j))).isoPullback_hom_fst
    rw [← Category.assoc, hm]
    change _ ≫ (Sigma.ι V (fun j ↦ t j.succ) ≫ Sigma.desc _) = _
    rw [Sigma.ι_comp_desc]
  have heq : finiteFamilyCechMap f (SimplexCategory.mk (n + 1)) = E.hom := by
    apply Sigma.hom_ext
    intro t
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc]
      change Sigma.ι
          (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          finiteFamilyCechMap f (SimplexCategory.mk (n + 1)) ≫
          WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) j =
        Sigma.ι _ t ≫ E.hom ≫ WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) j
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · rw [← Category.assoc, finiteFamilyCechMap, Sigma.ι_comp_desc,
          finiteFamilyCechInclusion_π]
        exact (hhead t).symm
      · have hπ : tail ≫ WidePullback.π (fun _ : Fin (n + 1) ↦ Sigma.desc f) j =
            WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) j.succ :=
          WidePullback.lift_π _ _ _ _ j
        rw [← Category.assoc, finiteFamilyCechMap, Sigma.ι_comp_desc,
          finiteFamilyCechInclusion_π]
        have hk := congrArg (fun k ↦ k ≫
          WidePullback.π (fun _ : Fin (n + 1) ↦ Sigma.desc f) j) (htail t)
        have he : Sigma.ι
              (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
              E.hom ≫ WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) j.succ =
            WidePullback.π (fun j ↦ f (t j)) j.succ ≫ Sigma.ι Z (t j.succ) := by
          have hm : mt t ≫ WidePullback.π
              (fun i : Fin (n + 1) ↦ f (t i.succ)) j =
              WidePullback.π (fun i : Fin (n + 2) ↦ f (t i)) j.succ :=
            WidePullback.lift_π _ _ _ _ j
          calc
            _ = mt t ≫ finiteFamilyCechInclusion f (SimplexCategory.mk n)
                (fun j ↦ t j.succ) ≫
                WidePullback.π (fun _ : Fin (n + 1) ↦ Sigma.desc f) j := by
              simpa only [Category.assoc, hπ] using hk
            _ = mt t ≫ (WidePullback.π (fun i : Fin (n + 1) ↦ f (t i.succ)) j ≫
                Sigma.ι Z (t j.succ)) := by rw [finiteFamilyCechInclusion_π]
            _ = (mt t ≫ WidePullback.π (fun i : Fin (n + 1) ↦ f (t i.succ)) j) ≫
                Sigma.ι Z (t j.succ) := (Category.assoc _ _ _).symm
            _ = _ := by rw [hm]
        exact he.symm
    · simp only [Category.assoc]
      change Sigma.ι
          (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
          finiteFamilyCechMap f (SimplexCategory.mk (n + 1)) ≫
          WidePullback.base (fun _ : Fin (n + 2) ↦ Sigma.desc f) =
        Sigma.ι _ t ≫ E.hom ≫ WidePullback.base (fun _ : Fin (n + 2) ↦ Sigma.desc f)
      rw [← Category.assoc, finiteFamilyCechMap, Sigma.ι_comp_desc,
        finiteFamilyCechInclusion_base]
      have hb : WidePullback.π (fun _ : Fin (n + 2) ↦ Sigma.desc f) 0 ≫ Sigma.desc f =
          WidePullback.base (fun _ : Fin (n + 2) ↦ Sigma.desc f) := WidePullback.π_arrow _ 0
      have hk := congrArg (fun k ↦ k ≫ Sigma.desc f) (hhead t)
      have he : Sigma.ι
            (fun t ↦ finiteFamilyCechComponent f (SimplexCategory.mk (n + 1)) t) t ≫
            E.hom ≫ WidePullback.base (fun _ : Fin (n + 2) ↦ Sigma.desc f) =
          WidePullback.base (fun j ↦ f (t j)) := by
        simpa only [Category.assoc, hb, Sigma.ι_comp_desc, WidePullback.π_arrow] using hk
      exact he.symm
  rw [heq]
  infer_instance

/-- 同じ有限余積の標準比較は、元の nerve の全ての次数で同型。 -/
theorem finiteFamilyCechMap_isIso [Finite ι] (n : ℕ) :
    IsIso (finiteFamilyCechMap f (SimplexCategory.mk n)) := by
  induction n with
  | zero => exact finiteFamilyCechMap_zero_isIso f
  | succ n ih =>
    haveI := ih
    exact finiteFamilyCechMap_succ_isIso f n

end SerrePositivity.AlgebraicGeometry
