module
public import SerrePositivity.InfinityCategories.Stable.JoinAssociator

/-! # join の結合同型の因子に関する自然性

概要：join の結合同型は三つの因子の射とも可換である。
方針：切断表示では切断を変えず各因子の射だけを作用させる。
規約：因子と射は任意。使われ方：S4 の二重 coslice の単体作用との両立。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：切断表示に二因子の射を作用させる。
方針：切断を保ち、左右の補った単体にそれぞれの射を作用させる。
規約：空次数も含む。使われ方：因子に関する結合の自然性。 -/
def stableAugJoinHom {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') (r : ℕ)
    (s : StableAugJoin K L r) : StableAugJoin K' L' r :=
  ⟨s.1, Join.augHom f s.1.val s.2.1, Join.augHom g (r - s.1.val) s.2.2⟩

/-- 概要：補った join の切断表示は二因子の射と可換。
方針：空次数は一点性、それ以外は joinMap の定義を使う。
規約：射は任意。使われ方：三因子の組み替えの自然性。 -/
lemma stableAugJoinEquiv_hom {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    (r : ℕ) (s : Join.augObj (join K L) r) :
    stableAugJoinEquiv K' L' r (Join.augHom (joinMap f g) r s) =
      stableAugJoinHom f g r (stableAugJoinEquiv K L r s) := by
  cases r with
  | zero => exact @Subsingleton.elim (StableAugJoin K' L' 0) inferInstance _ _
  | succ r => rfl

/-- 概要：補った単体の異種等式は射の作用で保たれる。
方針：頂点数を置換し、元の異種等式を通常の等式に戻す。
規約：空次数も含む。使われ方：移送した第三因子の自然性。 -/
lemma stableAugHom_heq {K L : SSet.{u}} (f : K ⟶ L) {r r' : ℕ} (hr : r = r')
    (x : Join.augObj K r) (y : Join.augObj K r') (hxy : HEq x y) :
    HEq (Join.augHom f r x) (Join.augHom f r' y) := by
  subst r'
  have h : x = y := eq_of_heq hxy
  subst y
  rfl

/-- 概要：三因子の切断表示の組み替えは因子の射と可換。
方針：切断と第一因子を比較し、右の join を表示へ戻して二因子を比較する。
規約：全ての空区間を許す。使われ方：結合同型の自然性。 -/
lemma stableAugReassociation_hom {K K' L L' M M' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') (r : ℕ)
    (s : StableAugJoin (join K L) M r) :
    stableAugReassociationEquiv K' L' M' r (stableAugJoinHom (joinMap f g) h r s) =
      stableAugJoinHom f (joinMap g h) r (stableAugReassociationEquiv K L M r s) := by
  let t := stableAugJoinHom (joinMap f g) h r s
  let ab := stableAugJoinEquiv K L s.1.val s.2.1
  let ab' := stableAugJoinEquiv K' L' t.1.val t.2.1
  have hnat : ab' = stableAugJoinHom f g s.1.val ab := stableAugJoinEquiv_hom f g _ _
  have ha : ab'.1.val = ab.1.val := congrArg (fun z ↦ z.1.val) hnat
  refine stableAugJoin_hext _ _ ha ?_ ?_
  · change HEq ab'.2.1 (Join.augHom f ab.1.val ab.2.1)
    exact stableAugJoin_left_heq hnat
  · change HEq (stableAugReassociationEquiv K' L' M' r t).2.2
      (Join.augHom (joinMap g h) (r - ab.1.val) (stableAugReassociationEquiv K L M r s).2.2)
    apply stableAugJoinEquiv_heq (congrArg (fun a ↦ r - a) ha)
    rw [stableAugReassociation_right_decode, stableAugJoinEquiv_hom,
      stableAugReassociation_right_decode]
    apply stableAugJoin_hext_total (congrArg (fun a ↦ r - a) ha)
    · exact congrArg (fun a ↦ s.1.val - a) ha
    · exact stableAugJoin_right_heq hnat
    · refine (cast_heq _ _).trans ?_
      apply stableAugHom_heq h (by
        have hsa : ab.1.val ≤ s.1.val := Nat.le_of_lt_succ ab.1.isLt
        have hsr : s.1.val ≤ r := Nat.le_of_lt_succ s.1.isLt
        change r - s.1.val = r - ab.1.val - (s.1.val - ab.1.val)
        omega)
      exact (cast_heq _ _).symm

/-- 概要：三因子の補った join の同値は因子の射と可換。
方針：切断表示の自然性と組み替えの自然性を合成する。
規約：各頂点数の型での式。使われ方：単体集合の結合同型の自然性。 -/
lemma stableAugJoinAssociatorEquiv_hom {K K' L L' M M' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') (r : ℕ)
    (s : Join.augObj (join (join K L) M) r) :
    stableAugJoinAssociatorEquiv K' L' M' r (Join.augHom (joinMap (joinMap f g) h) r s) =
      Join.augHom (joinMap f (joinMap g h)) r (stableAugJoinAssociatorEquiv K L M r s) := by
  apply (stableAugJoinEquiv K' (join L' M') r).injective
  change (stableAugJoinEquiv K' (join L' M') r)
    ((stableAugJoinEquiv K' (join L' M') r).symm
      (stableAugReassociationEquiv K' L' M' r
        (stableAugJoinEquiv (join K' L') M' r (Join.augHom (joinMap (joinMap f g) h) r s)))) = _
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_hom f (joinMap g h)]
  change _ = stableAugJoinHom f (joinMap g h) r
    ((stableAugJoinEquiv K (join L M) r)
      ((stableAugJoinEquiv K (join L M) r).symm
        (stableAugReassociationEquiv K L M r (stableAugJoinEquiv (join K L) M r s))))
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_hom, stableAugReassociation_hom]

/-- 概要：join の結合同型は三つの因子の射に関して自然。
方針：各次数の補った単体の自然性を射の等式へ束ねる。
規約：順方向の同型の射の等式。使われ方：二重 coslice の自然性。 -/
lemma stableJoinAssociator_naturality {K K' L L' M M' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    joinMap (joinMap f g) h ≫ (stableJoinAssociator K' L' M').hom =
      (stableJoinAssociator K L M).hom ≫ joinMap f (joinMap g h) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact stableAugJoinAssociatorEquiv_hom f g h (n + 1) s

end SerrePositivity.InfinityCategories
