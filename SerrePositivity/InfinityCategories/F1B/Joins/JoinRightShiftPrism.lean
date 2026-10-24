module

public import SerrePositivity.InfinityCategories.F1B.Joins.JoinShiftPrism

/-!
概要：join の右因子を外側へ移す prism と四境界。
方針：右直積比較、右因子の区間付き対角、逆結合同型を合成する。
規約：時間は第二因子、左因子は全時刻で固定する。
使われ方：右 Kan 拡張の局所比較錐と指定変換の輸送の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右直積比較は区間の終点と可換。
方針：零単体から終点への自然性と右直積比較の単位則を使う。
規約：時間は第二因子。
使われ方：右因子を移す prism の終点の計算。 -/
lemma joinTensorRight_ι₁ (A B : SSet.{u}) :
    (SSet.ι₁ : join A B ⟶ join A B ⊗ Δ[1]) ≫ joinTensorRight A B Δ[1] =
      joinMap (𝟙 A) (SSet.ι₁ : B ⟶ B ⊗ Δ[1]) := by
  have he (X : SSet.{u}) :
      fst X (Δ[0] : SSet.{u}) ≫ SSet.ι₁ = X ◁ (stdSimplex.δ (0 : Fin 2)) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      apply Fin.ext
      change (1 : ℕ) = ((SimplexCategory.δ (0 : Fin 2)).toOrderHom (t i)).val
      rw [Fin.eq_zero (t i)]
      rfl
  apply (cancel_epi (fst (join A B) (Δ[0] : SSet.{u}))).1
  rw [← Category.assoc, he, joinTensorRight_parameter, ← he B]
  have hc : joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u}) ≫ SSet.ι₁) =
      joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u})) ≫ joinMap (𝟙 A) SSet.ι₁ := by
    simpa only [Category.id_comp] using
      joinMap_comp (𝟙 A) (𝟙 A) (fst B (Δ[0] : SSet.{u})) SSet.ι₁
  rw [hc, ← Category.assoc, joinTensorRight_unit]

/-- 概要：右因子を join 全体の右側へ移す prism。
方針：右因子だけを二重化して逆結合する。
規約：始点は元の join の左包含。
使われ方：局所比較錐の右端への輸送。 -/
def joinRightShiftPrism (A B : SSet.{u}) :
    join A B ⊗ (Δ[1] : SSet.{u}) ⟶ join (join A B) B :=
  joinTensorRight A B Δ[1] ≫
    joinMap (𝟙 A) ((β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B) ≫
      (stableJoinAssociator A B B).inv

/-- 概要：右移動 prism の始点は join 全体の左包含。
方針：対角の始点を計算し、結合同型の左境界を消去する。
規約：時刻零。
使われ方：右輸送の start 条件。 -/
lemma joinRightShiftPrism_zero (A B : SSet.{u}) :
    SSet.ι₀ ≫ joinRightShiftPrism A B = joinInl (join A B) B := by
  rw [joinRightShiftPrism, ← Category.assoc, joinTensorRight_ι₀,
    ← Category.assoc, ← joinMap_comp, Category.id_comp]
  have h : (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) ≫
      (β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B = joinInl B B := by
    change prismEndpoint 0 B ≫ joinDiagonal B = _
    exact prismEndpoint_zero_joinDiagonal B
  rw [h]
  apply (cancel_mono (stableJoinAssociator A B B).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, stableJoinAssociator_inl]

/-- 概要：右移動 prism の終点は第一・第三因子からの包含。
方針：対角の終点と結合同型の中間因子の式を使う。
規約：時刻一。
使われ方：右輸送の比較錐の同定。 -/
lemma joinRightShiftPrism_one (A B : SSet.{u}) :
    SSet.ι₁ ≫ joinRightShiftPrism A B = joinMap (joinInl A B) (𝟙 B) := by
  rw [joinRightShiftPrism, ← Category.assoc, joinTensorRight_ι₁,
    ← Category.assoc, ← joinMap_comp, Category.id_comp]
  have h : (SSet.ι₁ : B ⟶ B ⊗ Δ[1]) ≫
      (β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B = joinInr B B := by
    change prismEndpoint 1 B ≫ joinDiagonal B = _
    exact prismEndpoint_one_joinDiagonal B
  rw [h, stableJoinAssociator_middle_inv]

/-- 概要：右移動 prism は左端を全時刻で固定する。
方針：右直積比較の左境界を計算し、結合同型で左端を戻す。
規約：時間の射影は第一射影。
使われ方：右輸送の fixedVertex 条件。 -/
lemma joinRightShiftPrism_left (A B : SSet.{u}) :
    (joinInl A B ▷ (Δ[1] : SSet.{u})) ≫ joinRightShiftPrism A B =
      fst A Δ[1] ≫ joinInl A B ≫ joinInl (join A B) B := by
  rw [joinRightShiftPrism, ← Category.assoc, joinTensorRight_inl,
    Category.assoc, ← Category.assoc (joinInl _ _), joinInl_joinMap, Category.id_comp]
  apply (cancel_mono (stableJoinAssociator A B B).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    stableJoinAssociator_inl, joinInl_joinMap, Category.id_comp]

/-- 概要：右移動 prism の右境界は指定対角の後に左 join の右包含を入れる。
方針：右直積比較の右境界と結合同型の後二因子の式を使う。
規約：この境界が右 Kan 拡張の指定自然変換を保持する。
使われ方：右輸送の diagram 条件。 -/
lemma joinRightShiftPrism_right (A B : SSet.{u}) :
    (joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ joinRightShiftPrism A B =
      (β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B ≫
        joinMap (joinInr A B) (𝟙 B) := by
  rw [joinRightShiftPrism, ← Category.assoc, joinTensorRight_inr,
    ← Category.assoc, joinInr_joinMap, Category.assoc,
    stableJoinAssociator_rightPair_inv, Category.assoc]

/-- 概要：右直積比較は join の両係数の射と可換。
方針：切断の右側の補った直積の第一成分に射を作用させる。
規約：第二因子のパラメータ P は任意。
使われ方：右 prism の両係数に関する自然性。 -/
lemma joinTensorRight_factors {A A' B B' : SSet.{u}} (P : SSet.{u})
    (f : A ⟶ A') (g : B ⟶ B') :
    (joinMap f g ▷ P) ≫ joinTensorRight A' B' P =
      joinTensorRight A B P ≫ joinMap f (g ▷ P) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨l, a, b⟩, p⟩
  change (⟨l, Join.augHom f l.val a,
      (Join.augTensorEquiv B' P (n + 1 - l.val)).symm
        (Join.augHom g (n + 1 - l.val) b,
          Join.augMap P (Join.suffixIncl (n + 1) l.val _) p)⟩ :
      Join.Simplex A' (B' ⊗ P) n) =
    ⟨l, Join.augHom f l.val a,
      Join.augHom (g ▷ P) (n + 1 - l.val)
        ((Join.augTensorEquiv B P (n + 1 - l.val)).symm
          (b, Join.augMap P (Join.suffixIncl (n + 1) l.val _) p))⟩
  apply Join.Simplex.ext _ _ (by apply Fin.ext; rfl)
  · rfl
  · exact (Join.augTensorEquiv_symm_augHomLeft g P _ b _).symm

/-- 概要：右移動 prism は両係数の射に自然。
方針：右直積比較、区間付き対角、結合同型の自然性を合わせる。
規約：時間は恒等射で保つ。
使われ方：局所比較錐の自然性を保つ輸送。 -/
lemma joinRightShiftPrism_naturality {A A' B B' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') :
    (joinMap f g ▷ (Δ[1] : SSet.{u})) ≫ joinRightShiftPrism A' B' =
      joinRightShiftPrism A B ≫ joinMap (joinMap f g) g := by
  have hd : (g ▷ (Δ[1] : SSet.{u})) ≫
      (β_ B' (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B' =
      (β_ B (Δ[1] : SSet.{u})).hom ≫ joinDiagonal B ≫ joinMap g g := by
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
      joinDiagonal_naturality]
  simp only [joinRightShiftPrism]
  rw [← Category.assoc, joinTensorRight_factors, Category.assoc,
    ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.comp_id, hd]
  apply (cancel_mono (stableJoinAssociator A' B' B').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [stableJoinAssociator_naturality]
  simp only [Iso.inv_hom_id_assoc, ← joinMap_comp,
    Category.id_comp, Category.assoc]

/-- 概要：右因子の移動を単体的ホモトピーとして束ねる。
方針：二つの端点の計算を用いる。
規約：元の join から外側の join への指定されたホモトピー。
使われ方：右 Kan 拡張の局所比較錐への後合成。 -/
def joinRightShiftHomotopy (A B : SSet.{u}) :
    SSet.Homotopy (joinInl (join A B) B) (joinMap (joinInl A B) (𝟙 B)) where
  h := joinRightShiftPrism A B
  h₀ := joinRightShiftPrism_zero A B
  h₁ := joinRightShiftPrism_one A B
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories
