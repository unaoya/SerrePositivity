module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionHorizontalFaithful

/-!
概要：端点の条件を満たす有限単調射から、四Homの実際の射を回収する。
方針：増大単体圏・二つの端点保存の圏・区間表示の既存の回収をまとめる。
規約：射の存在は仮定せず、全単射を実構成する。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの水平因子の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：minusから出る射の共通表示の対象は非空。
方針：混合Homと区間表示の個数を計算する。規約：実対象についてのinstance。
使われ方：Riehl–Verity Remark 3.3.8 の最小元の指定。 -/
instance walkingAdjunctionOrdinalCard_sourceMinus_neZero (Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom .minus Y) : NeZero (walkingAdjunctionOrdinalCard .minus Y A) := by
  cases Y <;> dsimp [walkingAdjunctionOrdinalCard] <;> infer_instance

/-- 概要：minusに入る射の共通表示の対象は非空。
方針：混合Homと区間表示の個数を計算する。規約：実対象についてのinstance。
使われ方：Riehl–Verity Remark 3.3.8 の最大元の指定。 -/
instance walkingAdjunctionOrdinalCard_targetMinus_neZero (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) : NeZero (walkingAdjunctionOrdinalCard X .minus A) := by
  cases X <;> dsimp [walkingAdjunctionOrdinalCard] <;> infer_instance

/-- 概要：中点の種類に応じた有限単調射の端点の条件。
方針：始点がminusなら最小元、終点がminusなら最大元の保存を要求する。
規約：空も許す型で全点を量化する。使われ方：Riehl–Verity Remark 3.3.8 の四Hom。 -/
def WalkingAdjunctionOrderBoundary (X Y : WalkingAdjunctionPoint)
    {m n : ℕ} (f : Fin m →o Fin n) : Prop :=
  (X = .minus → ∀ i : Fin m, i.val = 0 → (f i).val = 0) ∧
    (Y = .minus → ∀ i : Fin m, i.val + 1 = m → (f i).val + 1 = n)

/-- 概要：minusから出る射の共通表示は最小元を保つ。
方針：元の最小元保存と実区間表示の二つの場合を照合する。
規約：自然数の値で端点を指定する。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma walkingAdjunctionOrderHom_bottom {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B)
    (i : Fin (walkingAdjunctionOrdinalCard .minus Y A)) (hi : i.val = 0) :
    (walkingAdjunctionOrderHom f i).val = 0 := by
  cases Y
  · have hi₀ : i = 0 := Fin.ext hi
    subst i
    exact congrArg Fin.val f.property
  · have hi₀ : i = 0 := Fin.ext hi
    subst i
    exact congrArg Fin.val (ordinalIntervalMap_zero (augmentedOrderHom f.unop))

/-- 概要：minusに入る射の共通表示は最大元を保つ。
方針：最大元保存と実区間表示の二つの場合を照合する。
規約：点の個数によって最後の点を指定する。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma walkingAdjunctionOrderHom_top {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B)
    (i : Fin (walkingAdjunctionOrdinalCard X .minus A))
    (hi : i.val + 1 = walkingAdjunctionOrdinalCard X .minus A) :
    (walkingAdjunctionOrderHom f i).val + 1 = walkingAdjunctionOrdinalCard X .minus B := by
  cases X
  · have hi₁ : i = Fin.last A.obj.len := Fin.ext (by
      change i.val + 1 = A.obj.len + 1 at hi
      change i.val = A.obj.len
      omega)
    subst i
    have hf := congrArg Fin.val f.property
    change (f.hom.toOrderHom (Fin.last A.obj.len)).val + 1 = B.obj.len + 1
    change (f.hom.toOrderHom (Fin.last A.obj.len)).val = B.obj.len at hf
    omega
  · have hi₁ : i = Fin.last (augmentedOrdinalCard A.unop) := Fin.ext (by
      change i.val + 1 = augmentedOrdinalCard A.unop + 1 at hi
      change i.val = augmentedOrdinalCard A.unop
      omega)
    subst i
    have hf := congrArg Fin.val (ordinalIntervalMap_last (augmentedOrderHom f.unop))
    change (ordinalIntervalMap (augmentedOrderHom f.unop)
      (Fin.last (augmentedOrdinalCard A.unop))).val + 1 = augmentedOrdinalCard B.unop + 1
    change (ordinalIntervalMap (augmentedOrderHom f.unop)
      (Fin.last (augmentedOrdinalCard A.unop))).val = augmentedOrdinalCard B.unop at hf
    omega

/-- 概要：全ての実射の共通表示は指定の端点条件を満たす。
方針：二つの端点の保存を合わせる。規約：四Homの全射を含む。
使われ方：Riehl–Verity Remark 3.3.8 の同じ射の表示。 -/
lemma walkingAdjunctionOrderHom_boundary {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    WalkingAdjunctionOrderBoundary X Y (walkingAdjunctionOrderHom f) := by
  constructor
  · intro h i hi
    subst X
    exact walkingAdjunctionOrderHom_bottom f i hi
  · intro h i hi
    subst Y
    exact walkingAdjunctionOrderHom_top f i hi

/-- 概要：指定の端点条件を持つ有限単調射から実Homの射を作る。
方針：四つの場合で既存の回収を使う。規約：存在を引数として仮定しない。
使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の間の因子の構成。 -/
def walkingAdjunctionHomOfOrder {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y)
    (f : Fin (walkingAdjunctionOrdinalCard X Y A) →o Fin (walkingAdjunctionOrdinalCard X Y B))
    (hf : WalkingAdjunctionOrderBoundary X Y f) : A ⟶ B := by
  cases X <;> cases Y
  · exact augmentedHomOfOrder A B f
  · refine ⟨SimplexCategory.Hom.mk f, ?_⟩
    apply Fin.ext
    have h := hf.2 rfl (Fin.last A.obj.len) rfl
    change (f (Fin.last A.obj.len)).val = B.obj.len
    change (f (Fin.last A.obj.len)).val + 1 = B.obj.len + 1 at h
    omega
  · refine ⟨SimplexCategory.Hom.mk f, ?_⟩
    apply Fin.ext
    exact hf.1 rfl 0 rfl
  · have h₀ : f 0 = 0 := by apply Fin.ext; exact hf.1 rfl 0 rfl
    have h₁ : f (Fin.last (augmentedOrdinalCard A.unop)) =
        Fin.last (augmentedOrdinalCard B.unop) := by
      apply Fin.ext
      have h := hf.2 rfl (Fin.last (augmentedOrdinalCard A.unop)) rfl
      change (f (Fin.last (augmentedOrdinalCard A.unop))).val = augmentedOrdinalCard B.unop
      change (f (Fin.last (augmentedOrdinalCard A.unop))).val + 1 =
        augmentedOrdinalCard B.unop + 1 at h
      omega
    exact (augmentedHomOfOrder B.unop A.unop (ordinalRecoverMap f h₀ h₁)).op

/-- 概要：有限単調射を実Homに戻して表示しても元の全射を保つ。
方針：四つの既存の回収と表示の往復を使う。
規約：同じ端点条件。使われ方：Riehl–Verity Proposition 3.1.10 の残りの因子の射。 -/
lemma walkingAdjunctionOrderHom_ofOrder {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y)
    (f : Fin (walkingAdjunctionOrdinalCard X Y A) →o Fin (walkingAdjunctionOrdinalCard X Y B))
    (hf : WalkingAdjunctionOrderBoundary X Y f) :
    walkingAdjunctionOrderHom (walkingAdjunctionHomOfOrder A B f hf) = f := by
  cases X <;> cases Y
  · exact augmentedOrderHom_ofOrder A B f
  · rfl
  · rfl
  · have h₀ : f 0 = 0 := by apply Fin.ext; exact hf.1 rfl 0 rfl
    have h₁ : f (Fin.last (augmentedOrdinalCard A.unop)) =
        Fin.last (augmentedOrdinalCard B.unop) := by
      apply Fin.ext
      have h := hf.2 rfl (Fin.last (augmentedOrdinalCard A.unop)) rfl
      change (f (Fin.last (augmentedOrdinalCard A.unop))).val = augmentedOrdinalCard B.unop
      change (f (Fin.last (augmentedOrdinalCard A.unop))).val + 1 =
        augmentedOrdinalCard B.unop + 1 at h
      omega
    change ordinalIntervalMap (augmentedOrderHom
      (augmentedHomOfOrder B.unop A.unop (ordinalRecoverMap f h₀ h₁))) = f
    rw [augmentedOrderHom_ofOrder]
    exact ordinalIntervalMap_recover f h₀ h₁

/-- 概要：実Homの射の表示を戻しても元の射そのもの。
方針：表示の単射性と逆方向の往復を使う。規約：全四Homを含む。
使われ方：Riehl–Verity Remark 3.3.8 の忠実な回収。 -/
lemma walkingAdjunctionHomOfOrder_order {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    walkingAdjunctionHomOfOrder A B (walkingAdjunctionOrderHom f)
      (walkingAdjunctionOrderHom_boundary f) = f :=
  walkingAdjunctionOrderHom_injective
    (walkingAdjunctionOrderHom_ofOrder A B _ (walkingAdjunctionOrderHom_boundary f))

/-- 概要：実Homの射と指定の端点条件を持つ全有限単調射の実全単射。
方針：両方向の構成と二つの往復をまとめる。
規約：空の自己Homも含む。使われ方：Riehl–Verity Proposition 3.1.10 の実因子の回収。 -/
def walkingAdjunctionOrderProfileEquiv {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y) :
    (A ⟶ B) ≃ {f : Fin (walkingAdjunctionOrdinalCard X Y A) →o
      Fin (walkingAdjunctionOrdinalCard X Y B) // WalkingAdjunctionOrderBoundary X Y f} where
  toFun f := ⟨walkingAdjunctionOrderHom f, walkingAdjunctionOrderHom_boundary f⟩
  invFun f := walkingAdjunctionHomOfOrder A B f.val f.property
  left_inv := walkingAdjunctionHomOfOrder_order
  right_inv f := Subtype.ext (walkingAdjunctionOrderHom_ofOrder A B f.val f.property)

end SerrePositivity.InfinityCategories.HA.Monads
