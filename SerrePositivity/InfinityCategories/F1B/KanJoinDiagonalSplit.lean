module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinIntervalProjection
public import SerrePositivity.InfinityCategories.Core.JoinCylinderSimplex

/-!
概要：join の単体の切断と区間付き対角による左右の復元。
方針：切断の先頭・末尾への制限を元の左右の単体の包含として計算する。
規約：空の区間も補った次数で扱う。
使われ方：slice の普遍錐・余錐を relative join へ持ち上げる比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：join の単体を切断より前へ制限すると左の単体の包含が得られる。
方針：先頭区間の全頂点が左側にあるため切断を頂点数全体と計算する。
規約：左の頂点数が零でも成り立つ。
使われ方：区間付き対角の左成分の復元。 -/
lemma kanJoin_prefix {X Y : SSet.{u}} (n : ℕ) (s : (join X Y) _⦋n⦌) :
    Join.augMap (join X Y) (Join.prefixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) s =
      Join.augHom (joinInl X Y) s.1.val s.2.1 := by
  rcases s with ⟨⟨l, hl⟩, a, b⟩
  cases l with
  | zero => rfl
  | succ r =>
    let α := Join.prefixIncl (n + 1) (r + 1) (Nat.le_of_lt_succ hl)
    have hc : Join.pullCut α (r + 1) = r + 1 := by
      have h : ∀ i : Fin (r + 1), (α i).val < r + 1 := fun i ↦ i.isLt
      simp [Join.pullCut, h]
    change Join.simplexMap X Y α ⟨⟨r + 1, hl⟩, a, b⟩ = Join.Simplex.inl a
    rw [Join.simplexMap_eq_at X Y α ⟨r + 1, hl⟩ (r + 1) hc a b]
    have ha : Join.leftMapAt α (r + 1) (r + 1) hc = OrderHom.id := by
      ext i
      rfl
    rw [ha, Join.augMap_id]
    apply Join.Simplex.ext _ _ (by apply Fin.ext; rfl)
    · rfl
    · exact @Subsingleton.elim (Join.augObj Y (r + 1 - (r + 1)))
        (by simp only [Nat.sub_self, Join.augObj]; infer_instance) _ _

/-- 概要：join の単体を切断以後へ制限すると右の単体の包含が得られる。
方針：末尾区間の頂点は左側に入らないため切断を零と計算する。
規約：右の頂点数が零でも成り立つ。
使われ方：区間付き対角の右成分の復元。 -/
lemma kanJoin_suffix {X Y : SSet.{u}} (n : ℕ) (s : (join X Y) _⦋n⦌) :
    Join.augMap (join X Y) (Join.suffixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) s =
      Join.augHom (joinInr X Y) (n + 1 - s.1.val) s.2.2 := by
  rcases s with ⟨⟨l, hl⟩, a, b⟩
  by_cases hz : n + 1 - l = 0
  · have : Subsingleton (Join.augObj (join X Y) (n + 1 - l)) := by
      rw [hz]
      simp only [Join.augObj]
      infer_instance
    exact Subsingleton.elim _ _
  · let r := n - l
    have hr : n + 1 - l = r + 1 := by dsimp [r]; omega
    let α : Fin (r + 1) →o Fin (n + 1) :=
      { toFun := fun i ↦ ⟨l + i.val, by have := i.isLt; omega⟩
        monotone' := fun _ _ h ↦ Nat.add_le_add_left h l }
    have hc : Join.pullCut α l = 0 := by
      have h : ∀ i : Fin (r + 1), ¬ (α i).val < l := by intro i; dsimp [α]; omega
      simp [Join.pullCut, h]
    have hh := Join.simplexMap_eq_at X Y α ⟨l, hl⟩ 0 hc a b
    have hmap := Join.augMap_congr (join X Y) hr rfl
      (Join.suffixIncl (n + 1) l (Nat.le_of_lt_succ hl)) α
      (by intro i j hij; dsimp [Join.suffixIncl, α]; omega)
      (⟨⟨l, hl⟩, a, b⟩ : (join X Y) _⦋n⦌) _ rfl
    apply (Equiv.cast (congrArg (Join.augObj (join X Y)) hr)).injective
    refine hmap.trans ?_
    change Join.simplexMap X Y α ⟨⟨l, hl⟩, a, b⟩ = _
    rw [hh]
    change _ = cast (congrArg (Join.augObj (join X Y)) hr)
      (Join.augHom (joinInr X Y) (n + 1 - l) b)
    rw [Join.augHom_cast (joinInr X Y) hr b]
    change _ = Join.Simplex.inr (cast (congrArg (Join.augObj Y) hr) b)
    apply Join.Simplex.ext _ _ (by apply Fin.ext; rfl)
    · exact @Subsingleton.elim (Join.augObj X 0)
        (by dsimp only [Join.augObj]; infer_instance) _ _
    · exact (Join.augMap_congr Y (by omega : r + 1 - 0 = r + 1) hr
        (Join.rightMapAt α l 0 hc) OrderHom.id
        (by intro i j hij; change l + (0 + i.val) - l = j.val; omega)
        b (cast (congrArg (Join.augObj Y) hr) b) rfl).trans (Join.augMap_id Y _ _)

/-- 概要：join の区間と単体そのものを対角へ写すと、左右の包含の join になる。
方針：区間の切断を元の切断と同定し、先頭・末尾の復元式を使う。
規約：左右の単体集合は任意。
使われ方：任意の join 上の図式を relative join の引き戻しへ持ち上げる。 -/
lemma kanJoinDiagonal_split (X Y : SSet.{u}) :
    lift (joinIntervalProjection X Y) (𝟙 (join X Y)) ≫ joinDiagonal (join X Y) =
      joinMap (joinInl X Y) (joinInr X Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  let t := (joinIntervalProjection X Y).app (Opposite.op ⦋n⦌) s
  let z := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  have hc : z.1 = s.1 := by
    apply Fin.ext
    exact (intervalJoin_cut n t).trans (joinIntervalProjection_app_cut X Y n s)
  change (joinCylinderMap (join X Y) (join X Y)).app (Opposite.op ⦋n⦌) ((s, t), s) = _
  rw [joinCylinderMap_app]
  change (⟨z.1,
    Join.augMap (join X Y) (Join.prefixIncl (n + 1) z.1.val _) s,
    Join.augMap (join X Y) (Join.suffixIncl (n + 1) z.1.val _) s⟩ :
      Join.Simplex (join X Y) (join X Y) n) = _
  refine Join.Simplex.ext _ _ hc ?_ ?_
  · exact (Join.augMap_congr (join X Y) (congrArg Fin.val hc) rfl
      (Join.prefixIncl (n + 1) z.1.val _) (Join.prefixIncl (n + 1) s.1.val _)
      (by intro i j hij; exact hij) s s rfl).trans (kanJoin_prefix n s)
  · exact (Join.augMap_congr (join X Y)
      (congrArg (fun l : Fin (n + 2) ↦ n + 1 - l.val) hc) rfl
      (Join.suffixIncl (n + 1) z.1.val _) (Join.suffixIncl (n + 1) s.1.val _)
      (by
        intro i j hij
        have hval := congrArg Fin.val hc
        change z.1.val + i.val = s.1.val + j.val
        omega) s s rfl).trans (kanJoin_suffix n s)

/-- 概要：join 上の任意の図式の区間付き対角は左右の制限の join と一致する。
方針：join 自体の復元式を係数の自然性で後合成する。
規約：図式は joinMap として与えられていなくてもよい。
使われ方：slice の普遍余錐の relative join への標準持ち上げ。 -/
lemma kanJoinDiagonal_split_map {X Y C : SSet.{u}} (f : join X Y ⟶ C) :
    lift (joinIntervalProjection X Y) f ≫ joinDiagonal C =
      joinMap (joinInl X Y ≫ f) (joinInr X Y ≫ f) := by
  have h : lift (joinIntervalProjection X Y) f =
      lift (joinIntervalProjection X Y) (𝟙 (join X Y)) ≫
        ((Δ[1] : SSet.{u}) ◁ f) := rfl
  rw [h, Category.assoc, joinDiagonal_naturality, ← Category.assoc,
    kanJoinDiagonal_split, joinMap_comp]

end SerrePositivity.InfinityCategories
