module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：右 pinched 写像空間と頂点上の slice fiber の比較。
方針：標準単体と点との join の同型を各次数で用いる。
規約：右端が終点、左面が始点に定値。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.6.5（Tag 01KW）。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：点を後置した連結と終点固定延長は可換。
方針：切断の左右で Fin.castSucc と Fin.last の公式を使う。
規約：右因子の頂点数は一つ。
使われ方：HTT §1.2.8、Kerodon §4.6.5（Tag 01KW） の写像空間の自然性。 -/
lemma concat_extendOrderHom {m n r : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (ℓ : ℕ) (hℓ : ℓ ≤ r) (f : Fin ℓ →o Fin (m + 1)) (g : Fin (r - ℓ) →o Fin 1)
    (i : Fin r) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ (α.comp f) g i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i)).val := by
  by_cases hi : i.val < ℓ
  · have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i = (f ⟨i.val, hi⟩).castSucc := Fin.ext (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi]; rfl)
    rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi]
    rfl
  · have hge : ℓ ≤ i.val := by omega
    have hg : g ⟨i.val - ℓ, by have := i.isLt; omega⟩ = 0 := Subsingleton.elim _ _
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i = Fin.last (m + 1) := Fin.ext (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hge, hg]; rfl)
    rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hge, hg]
    rfl

/-- 概要：標準単体と点の join の同型は左因子の射に自然。
方針：連結写像と終点固定延長の可換性を単体ごとに使う。
規約：n+0+1 は n+1 と定義的に同じ次元。
使われ方：HTT §1.2.8、Kerodon §4.6.5（Tag 01KW） の slice fiber 同定。 -/
lemma joinStdSimplexIso_rightPoint_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α) (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.map α) _ s.2.1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 Δ[0]) _ s.2.2)) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv_augHom]
  exact concat_extendOrderHom α.toOrderHom _ _ _ _ i

/-- 概要：左因子の包含は最終頂点以外の面になる。
方針：Yoneda 表示の恒等単体を連結写像で評価する。
規約：頂点の番号は変えない。
使われ方：HTT §1.2.8、Kerodon §4.6.5（Tag 01KW） の始点固定条件。 -/
lemma joinStdSimplexIso_rightPoint_inl (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (n + 1) (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n (n + 1) (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 (n + 1 - (n + 1)) (by
      simp only [Nat.sub_self, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj]; exact PUnit.unit)) i).val = i.val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ i.isLt]
  rfl

/-- 概要：右因子の包含は最終頂点になる。
方針：既存の最終頂点の計算を零単体の Yoneda 同値で読む。
規約：右因子は標準零単体。
使われ方：HTT §1.2.8、Kerodon §4.6.5（Tag 01KW） の終点固定条件。 -/
lemma joinStdSimplexIso_rightPoint_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr_vertex]
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：右 pinched 単体を slice 射影の始点上の fiber の単体にする。
方針：join の同型で移し、左右の制限を固定条件で確認する。
規約：始点 x、終点 y。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.6.5（Tag 01KW）。 -/
def pinchedSimplexToFiber {X : SSet.{u}} {x y : X _⦋0⦌} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x) _⦋n⦌ := by
  refine ⟨⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm s.val, ?_⟩, ?_⟩
  · rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
      SSet.yonedaEquiv_symm_naturality_left, s.target]
  · change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm s.val)) = _
    rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl,
      SSet.yonedaEquiv_symm_naturality_left, s.source, Equiv.apply_symm_apply]

/-- 概要：右 pinched 写像空間から slice 射影の fiber への射。
方針：各次数の構成が終点固定延長に自然であることを使う。
規約：quasicategory 性を前提にしない。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.6.5（Tag 01KW）。 -/
def pinchedHomToSliceFiber {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x where
  app _ := ↾pinchedSimplexToFiber
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫
      SSet.yonedaEquiv.symm (X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op s.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 Δ[0]) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm s.val)
    rw [← SSet.yonedaEquiv_symm_naturality_left]
    rw [← Category.assoc]
    exact congrArg (fun f ↦ f ≫ SSet.yonedaEquiv.symm s.val)
      (joinStdSimplexIso_rightPoint_naturality α.unop).symm

/-- 概要：slice 射影の fiber の単体を右 pinched 単体に戻す。
方針：join の逆同型を合成して左右の固定条件を読む。
規約：各次数での逆写像。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.6.5（Tag 01KW）。 -/
def fiberSimplexToPinched {X : SSet.{u}} {x y : X _⦋0⦌} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n where
  val := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ s.val.val)
  source := by
    rw [SSet.yonedaEquiv_naturality]
    have h := joinStdSimplexIso_rightPoint_inl.{u} n
    rw [← h, Category.assoc, Iso.hom_inv_id_assoc]
    exact s.property
  target := by
    rw [SSet.yonedaEquiv_naturality]
    have h := joinStdSimplexIso_rightPoint_inr.{u} n
    rw [← h, Category.assoc, Iso.hom_inv_id_assoc, s.val.property,
      Equiv.apply_symm_apply]

/-- 概要：右 pinched 写像空間は slice 射影の fiber と同型。
方針：各次数の二つの構成が join の同型の両逆であることを使う。
規約：任意の単体集合で成り立つ厳密な同型。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.6.5（Tag 01KW）。 -/
noncomputable def pinchedHomSliceFiberIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x := by
  have h (n : SimplexCategoryᵒᵖ) : Function.Bijective ((pinchedHomToSliceFiber x y).app n) := by
    cases n with | op n => cases n with | mk n =>
      apply Function.bijective_iff_has_inverse.mpr
      refine ⟨fiberSimplexToPinched, ?_, ?_⟩
      · intro s
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
        change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm s.val)) = s.val
        rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
      · intro s
        apply Subtype.ext
        apply Subtype.ext
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
          (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ s.val.val)) = s.val.val
        rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  have : IsIso (pinchedHomToSliceFiber x y) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    rw [isIso_iff_bijective]
    exact h n
  exact asIso (pinchedHomToSliceFiber x y)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
