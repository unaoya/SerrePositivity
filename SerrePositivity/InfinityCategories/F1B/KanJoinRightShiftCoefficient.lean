module

public import SerrePositivity.InfinityCategories.F1B.KanJoinRightCutRestriction
public import SerrePositivity.InfinityCategories.F1B.KanJoinShiftCoefficient

/-!
概要：右移動 prism の係数の可換性を全単体で検証する。
方針：右因子を二分した逆結合同型の表示を、元の join の先頭・末尾制限と比較する。
規約：切断以後での制限、空次数と頂点数の移送を含む。
使われ方：右比較錐の移動 prism の relative join への持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子を二分した表示は、元の join の先頭を左因子にした表示へ逆結合する。
方針：先頭制限の切断を復号し、結合同型の後二因子を比較する。
規約：元の切断以上の m を用いる。
使われ方：右移動 prism の単体の正規形。 -/
lemma kanAugJoin_rightPartialSplit_reassociate {A B : SSet.{u}} (r : ℕ)
    (s : StableAugJoin A B r) (m : ℕ) (hm : m ≤ r) (hl : s.1.val ≤ m) :
    let v : StableAugJoin B B (r - s.1.val) :=
      ⟨⟨m - s.1.val, by omega⟩,
        Join.augMap B (Join.prefixIncl (r - s.1.val) (m - s.1.val) (by omega)) s.2.2,
        Join.augMap B (Join.suffixIncl (r - s.1.val) (m - s.1.val) (by omega)) s.2.2⟩
    let w : StableAugJoin (join A B) B r :=
      ⟨⟨m, by omega⟩,
        Join.augMap (join A B) (Join.prefixIncl r m hm) ((stableAugJoinEquiv A B r).symm s),
        cast (congrArg (Join.augObj B) (by omega :
          r - s.1.val - (m - s.1.val) = r - m)) v.2.2⟩
    stableAugReassociationEquiv A B B r w =
      ⟨s.1, s.2.1, (stableAugJoinEquiv B B (r - s.1.val)).symm v⟩ := by
  intro v w
  let v' := stableAugJoinEquiv A B m w.2.1
  have hv : v' = ⟨⟨s.1.val, by omega⟩, s.2.1, v.2.1⟩ :=
    kanAugJoin_prefix_after r s m hm hl
  have hc : (stableAugReassociationEquiv A B B r w).1.val = s.1.val :=
    congrArg (fun z ↦ z.1.val) hv
  apply stableAugJoin_hext _ _ hc
  · change HEq v'.2.1 s.2.1
    exact stableAugJoin_left_heq hv
  · apply stableAugJoinEquiv_heq (congrArg (fun a ↦ r - a) hc)
    rw [Equiv.apply_symm_apply]
    change HEq
      (stableAugJoinEquiv B B (r - v'.1.val) (stableAugReassociationEquiv A B B r w).2.2) v
    refine (heq_of_eq (stableAugReassociation_right_decode A B B r w)).trans ?_
    apply stableAugJoin_hext_total (congrArg (fun a ↦ r - a) hc)
    · change m - v'.1.val = m - s.1.val
      have h : v'.1.val = s.1.val := congrArg (fun z ↦ z.1.val) hv
      omega
    · exact stableAugJoin_right_heq hv
    · exact (cast_heq _ _).trans (cast_heq _ _)

/-- 概要：時間を第二因子に置いた対角も時間の切断で二因子へ制限する。
方針：空次数は一点性、正次数は joinCylinderMap の単体表示を使う。
規約：braiding を対角の直前に入れる。
使われ方：右 prism の内側の対角の計算。 -/
lemma kanAugJoinRightDiagonal_formula (B : SSet.{u}) (r : ℕ)
    (b : Join.augObj B r) (t : Join.augObj (Δ[1] : SSet.{u}) r) :
    let z := stableAugJoinEquiv (Δ[0] : SSet.{u}) Δ[0] r
      (Join.augHom (joinStdSimplexIso.{u} 0 0).inv r t)
    stableAugJoinEquiv B B r
      (Join.augHom ((β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B) r
        ((Join.augTensorEquiv B Δ[1] r).symm (b, t))) =
      ⟨z.1, Join.augMap B (Join.prefixIncl r z.1.val (Nat.le_of_lt_succ z.1.isLt)) b,
        Join.augMap B (Join.suffixIncl r z.1.val (Nat.le_of_lt_succ z.1.isLt)) b⟩ := by
  cases r with
  | zero => rfl
  | succ n =>
    change (joinCylinderMap B B).app (Opposite.op ⦋n⦌) ((b, t), b) = _
    exact joinCylinderMap_app B B n b t b

/-- 概要：右移動 prism は移動後の切断で元の join を先頭と末尾に分ける。
方針：候補の表示を順方向へ結合して、右因子の対角の表示と比較する。
規約：移動後の切断は元の切断と右因子上の時間の切断の和。
使われ方：右 prism の係数の可換性を全単体で検査する。 -/
lemma kanJoinRightShiftPrism_app_normal {A B : SSet.{u}} (n : ℕ)
    (s : StableAugJoin A B (n + 1)) (t : Join.augObj (Δ[1] : SSet.{u}) (n + 1)) :
    let tb := Join.augMap (Δ[1] : SSet.{u})
      (Join.suffixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) t
    let z := stableAugJoinEquiv (Δ[0] : SSet.{u}) Δ[0] (n + 1 - s.1.val)
      (Join.augHom (joinStdSimplexIso.{u} 0 0).inv (n + 1 - s.1.val) tb)
    let m := s.1.val + z.1.val
    (kanJoinRightShiftPrism A B).app (Opposite.op ⦋n⦌) (s, t) =
      (⟨⟨m, by
          have hz : z.1.val < n + 1 - s.1.val + 1 := z.1.isLt
          have hs : s.1.val < n + 2 := s.1.isLt
          omega⟩,
        Join.augMap (join A B) (Join.prefixIncl (n + 1) m (by
          have hz : z.1.val < n + 1 - s.1.val + 1 := z.1.isLt
          have hs : s.1.val < n + 2 := s.1.isLt
          omega)) s,
        cast (congrArg (Join.augObj B) (by omega :
          n + 1 - s.1.val - z.1.val = n + 1 - m))
          (Join.augMap B
            (Join.suffixIncl (n + 1 - s.1.val) z.1.val (Nat.le_of_lt_succ z.1.isLt)) s.2.2)⟩ :
          Join.Simplex (join A B) B n) := by
  intro tb z m
  have hm : m ≤ n + 1 := by
    have hz : z.1.val < n + 1 - s.1.val + 1 := z.1.isLt
    have hs : s.1.val < n + 2 := s.1.isLt
    dsimp [m]
    omega
  have hl : s.1.val ≤ m := Nat.le_add_right _ _
  let v : StableAugJoin B B (n + 1 - s.1.val) :=
    ⟨z.1,
      Join.augMap B (Join.prefixIncl (n + 1 - s.1.val) z.1.val
        (Nat.le_of_lt_succ z.1.isLt)) s.2.2,
      Join.augMap B (Join.suffixIncl (n + 1 - s.1.val) z.1.val
        (Nat.le_of_lt_succ z.1.isLt)) s.2.2⟩
  have hd : Join.augHom ((β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B)
      (n + 1 - s.1.val)
      ((Join.augTensorEquiv B Δ[1] (n + 1 - s.1.val)).symm (s.2.2, tb)) =
        (stableAugJoinEquiv B B (n + 1 - s.1.val)).symm v := by
    apply (stableAugJoinEquiv B B (n + 1 - s.1.val)).injective
    rw [Equiv.apply_symm_apply]
    exact kanAugJoinRightDiagonal_formula B (n + 1 - s.1.val) s.2.2 tb
  apply (stableAugJoinAssociatorEquiv A B B (n + 1)).injective
  change ((kanJoinRightShiftPrism A B ≫ (stableJoinAssociator A B B).hom).app
    (Opposite.op ⦋n⦌)) (s, t) = _
  simp only [kanJoinRightShiftPrism, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (stableAugJoinEquiv A (join B B) (n + 1)).injective
  change (⟨s.1, Join.augHom (𝟙 A) s.1.val s.2.1,
    Join.augHom ((β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B) (n + 1 - s.1.val)
      ((Join.augTensorEquiv B Δ[1] (n + 1 - s.1.val)).symm (s.2.2, tb))⟩ :
      StableAugJoin A (join B B) (n + 1)) = _
  rw [hd, Join.augHom_id]
  symm
  let v' : StableAugJoin B B (n + 1 - s.1.val) :=
    ⟨⟨m - s.1.val, by omega⟩,
      Join.augMap B (Join.prefixIncl (n + 1 - s.1.val) (m - s.1.val) (by omega)) s.2.2,
      Join.augMap B (Join.suffixIncl (n + 1 - s.1.val) (m - s.1.val) (by omega)) s.2.2⟩
  have hk : m - s.1.val = z.1.val := by dsimp [m]; omega
  have hv : v' = v := by
    apply stableAugJoin_hext _ _ hk
    · exact stableAugMap_heq B hk rfl _ _ (by intro i j hij; exact hij) _ _ HEq.rfl
    · exact stableAugMap_heq B (congrArg (fun k ↦ n + 1 - s.1.val - k) hk) rfl _ _
        (by intro i j hij; change m - s.1.val + i.val = z.1.val + j.val; omega) _ _ HEq.rfl
  let w' : StableAugJoin (join A B) B (n + 1) :=
    ⟨⟨m, by omega⟩,
      Join.augMap (join A B) (Join.prefixIncl (n + 1) m hm) s,
      cast (congrArg (Join.augObj B) (by omega :
        n + 1 - s.1.val - (m - s.1.val) = n + 1 - m)) v'.2.2⟩
  let w : StableAugJoin (join A B) B (n + 1) :=
    ⟨⟨m, by omega⟩,
      Join.augMap (join A B) (Join.prefixIncl (n + 1) m hm) s,
      cast (congrArg (Join.augObj B) (by omega :
        n + 1 - s.1.val - z.1.val = n + 1 - m)) v.2.2⟩
  have hw : w' = w := by
    refine stableAugJoin_hext w' w rfl HEq.rfl ?_
    exact (cast_heq _ _).trans ((stableAugJoin_right_heq hv).trans (cast_heq _ _).symm)
  have h : stableAugReassociationEquiv A B B (n + 1) w' =
      ⟨s.1, s.2.1, (stableAugJoinEquiv B B (n + 1 - s.1.val)).symm v'⟩ :=
    kanAugJoin_rightPartialSplit_reassociate (n + 1) s m hm hl
  rw [hw, hv] at h
  exact h

/-- 概要：右移動 prism の係数は元の join の対角に、移動後の時間とともに入る。
方針：単体の正規形と対角の先頭・末尾制限の公式を比較する。
規約：全ての高次単体での等式。
使われ方：右比較錐の prism の relative join の pullback 条件。 -/
lemma kanJoinRightShiftPrism_coefficient (A B : SSet.{u}) :
    kanJoinRightShiftPrism A B ≫ joinMap (𝟙 (join A B)) (joinInr A B) =
      lift (kanJoinRightShiftPrism A B ≫ joinIntervalProjection (join A B) B)
        (fst (join A B) (Δ[1] : SSet.{u})) ≫ joinDiagonal (join A B) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  let tb := Join.augMap (Δ[1] : SSet.{u})
    (Join.suffixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) t
  let z := stableAugJoinEquiv (Δ[0] : SSet.{u}) Δ[0] (n + 1 - s.1.val)
    (Join.augHom (joinStdSimplexIso.{u} 0 0).inv (n + 1 - s.1.val) tb)
  let m := s.1.val + z.1.val
  have hmn : m ≤ n + 1 := by
    have hz : z.1.val < n + 1 - s.1.val + 1 := z.1.isLt
    have hs : s.1.val < n + 2 := s.1.isLt
    dsimp [m]
    omega
  have hl : s.1.val ≤ m := Nat.le_add_right _ _
  have hk : m - s.1.val = z.1.val := by dsimp [m]; omega
  let b := cast (congrArg (Join.augObj B) (by omega :
      n + 1 - s.1.val - z.1.val = n + 1 - m))
    (Join.augMap B (Join.suffixIncl (n + 1 - s.1.val) z.1.val
      (Nat.le_of_lt_succ z.1.isLt)) s.2.2)
  let u := (kanJoinRightShiftPrism A B).app (Opposite.op ⦋n⦌) (s, t)
  let τ := (joinIntervalProjection (join A B) B).app (Opposite.op ⦋n⦌) u
  let e := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) τ
  have hu : u = (⟨⟨m, by omega⟩,
      Join.augMap (join A B) (Join.prefixIncl (n + 1) m hmn) s, b⟩ :
        Join.Simplex (join A B) B n) := kanJoinRightShiftPrism_app_normal n s t
  have hcut : e.1.val = m :=
    (intervalJoin_cut n τ).trans
      ((joinIntervalProjection_app_cut (join A B) B n u).trans
        (congrArg (fun q ↦ q.1.val) hu))
  have hsuffix : Join.augMap (join A B) (Join.suffixIncl (n + 1) m hmn) s =
      Join.augHom (joinInr A B) (n + 1 - m) b := by
    refine (kanAugJoin_suffix_after (n + 1) s m hmn hl).trans ?_
    apply congrArg (Join.augHom (joinInr A B) (n + 1 - m))
    apply eq_of_heq
    refine (cast_heq _ _).trans ?_
    refine (stableAugMap_heq B (congrArg (fun k ↦ n + 1 - s.1.val - k) hk) rfl
      (Join.suffixIncl (n + 1 - s.1.val) (m - s.1.val) (by omega))
      (Join.suffixIncl (n + 1 - s.1.val) z.1.val (Nat.le_of_lt_succ z.1.isLt))
      (by intro i j hij; change m - s.1.val + i.val = z.1.val + j.val; omega)
      s.2.2 s.2.2 HEq.rfl).trans ?_
    exact (cast_heq _ _).symm
  change (joinMap (𝟙 (join A B)) (joinInr A B)).app (Opposite.op ⦋n⦌) u =
    (joinCylinderMap (join A B) (join A B)).app (Opposite.op ⦋n⦌) ((s, τ), s)
  rw [hu, joinCylinderMap_app]
  change (⟨⟨m, _⟩,
      Join.augHom (𝟙 (join A B)) m
        (Join.augMap (join A B) (Join.prefixIncl (n + 1) m hmn) s),
      Join.augHom (joinInr A B) (n + 1 - m) b⟩ :
        Join.Simplex (join A B) (join A B) n) =
      ⟨e.1, Join.augMap (join A B)
        (Join.prefixIncl (n + 1) e.1.val (Nat.le_of_lt_succ e.1.isLt)) s,
        Join.augMap (join A B)
          (Join.suffixIncl (n + 1) e.1.val (Nat.le_of_lt_succ e.1.isLt)) s⟩
  rw [Join.augHom_id, ← hsuffix]
  symm
  apply Join.Simplex.ext _ _ (Fin.ext hcut)
  · exact Join.augMap_congr (join A B) hcut rfl
      (Join.prefixIncl (n + 1) e.1.val (Nat.le_of_lt_succ e.1.isLt))
      (Join.prefixIncl (n + 1) m hmn) (by intro i j hij; exact hij) s s rfl
  · exact Join.augMap_congr (join A B) (congrArg (fun c ↦ n + 1 - c) hcut) rfl
      (Join.suffixIncl (n + 1) e.1.val (Nat.le_of_lt_succ e.1.isLt))
      (Join.suffixIncl (n + 1) m hmn) (by
        intro i j hij
        change e.1.val + i.val = m + j.val
        omega) s s rfl

end SerrePositivity.InfinityCategories
