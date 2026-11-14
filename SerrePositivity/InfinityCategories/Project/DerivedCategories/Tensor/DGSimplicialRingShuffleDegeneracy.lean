module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingShuffleNative
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingNormalization
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEdges
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
/-!
概要：実 shuffle 積の退化零化と正規化射影の整合性。
方針：共通退化因子・PInfty の補射影と元の実結合・単位を接続する。
規約：非可換な積の順序と元の全次数を保つ。使われ方：β5(g) の正規化 dg 代数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open EInfinity.BarrattEccles
open scoped _root_.Simplicial
lemma simplex_pair_common_degeneracy {n p q : ℕ}
    (a : ⦋n⦌ ⟶ ⦋p⦌) (b : ⦋n⦌ ⟶ ⦋q⦌) (j : Fin n)
    (ha : a.toOrderHom j.castSucc = a.toOrderHom j.succ)
    (hb : b.toOrderHom j.castSucc = b.toOrderHom j.succ) :
    ∃ (T : SimplexCategory) (θ : ⦋n⦌ ⟶ T) (a' : T ⟶ ⦋p⦌) (b' : T ⟶ ⦋q⦌),
      ¬Mono θ ∧ a = θ ≫ a' ∧ b = θ ≫ b' := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    obtain ⟨a', ha'⟩ := SimplexCategory.eq_σ_comp_of_not_injective' a j ha
    obtain ⟨b', hb'⟩ := SimplexCategory.eq_σ_comp_of_not_injective' b j hb
    refine ⟨⦋n⦌, SimplexCategory.σ j, a', b', ?_, ha', hb'⟩
    intro h
    have he := @SimplexCategory.le_of_mono _ _ (SimplexCategory.σ j) h
    exact Nat.not_succ_le_self n he
lemma projectedRingProduct_zero_of_common_degeneracy
    (A : SimplicialObject RingCat.{u}) {n p q : ℕ}
    (a : ⦋n⦌ ⟶ ⦋p⦌) (b : ⦋n⦌ ⟶ ⦋q⦌) (j : Fin n)
    (ha : a.toOrderHom j.castSucc = a.toOrderHom j.succ)
    (hb : b.toOrderHom j.castSucc = b.toOrderHom j.succ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f n).hom
      ((A.map a.op).hom x * (A.map b.op).hom y) = 0 := by
  obtain ⟨T, θ, a', b', hθ, ha', hb'⟩ := simplex_pair_common_degeneracy a b j ha hb
  have h := degeneracy_comp_PInfty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) n θ hθ
  have hv := congrArg (fun f ↦ f.hom ((A.map a'.op).hom x * (A.map b'.op).hom y)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hv
  rw [ha', hb', op_comp, op_comp, A.map_comp, A.map_comp,
    RingCat.hom_comp, RingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
  exact hv
lemma ringShuffleTerm_degenerate_left (A : SimplicialObject RingCat.{u}) {p q : ℕ}
    (s : ShufflePath (p + 1) q) (i : Fin (p + 1))
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + 1 + q)).hom
      ((A.map s.horizontalMap.op).hom ((A.σ i).hom x) *
        (A.map s.verticalMap.op).hom y) = 0 := by
  obtain ⟨j, h0, h1, hv⟩ := s.horizontal_edge i
  have hh : (s.horizontalMap ≫ SimplexCategory.σ i).toOrderHom j.castSucc =
      (s.horizontalMap ≫ SimplexCategory.σ i).toOrderHom j.succ := by
    change i.predAbove (s.horizontal j.castSucc) = i.predAbove (s.horizontal j.succ)
    rw [h0, h1, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have h := projectedRingProduct_zero_of_common_degeneracy A
    (s.horizontalMap ≫ SimplexCategory.σ i) s.verticalMap j hh hv x y
  simpa only [op_comp, A.map_comp, RingCat.hom_comp, RingHom.comp_apply,
    SimplicialObject.σ_def] using h
lemma ringShuffleTerm_degenerate_right (A : SimplicialObject RingCat.{u}) {p q : ℕ}
    (s : ShufflePath p (q + 1)) (i : Fin (q + 1))
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + (q + 1))).hom
      ((A.map s.horizontalMap.op).hom x *
        (A.map s.verticalMap.op).hom ((A.σ i).hom y)) = 0 := by
  obtain ⟨j, h0, h1, hh⟩ := s.vertical_edge i
  have hv : (s.verticalMap ≫ SimplexCategory.σ i).toOrderHom j.castSucc =
      (s.verticalMap ≫ SimplexCategory.σ i).toOrderHom j.succ := by
    change i.predAbove (s.vertical j.castSucc) = i.predAbove (s.vertical j.succ)
    rw [h0, h1, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  have h := projectedRingProduct_zero_of_common_degeneracy A
    s.horizontalMap (s.verticalMap ≫ SimplexCategory.σ i) j hh hv x y
  simpa only [op_comp, A.map_comp, RingCat.hom_comp, RingHom.comp_apply,
    SimplicialObject.σ_def] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
