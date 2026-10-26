module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiChartTransport
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiTransportMap
/-!
概要：全基点チャートを Kan 空間の実同値で輸送する。
方針：実逆射の π 同型を使い、指定道の不変性は同じ逆射の後合成で運ぶ。
規約：元の全空間比較の逆データを固定する。
使われ方：線形 Hom チャートを native 評価値とその実辺作用へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable {X Y X' Y' : SSet.{u}} [KanComplex X] [KanComplex Y]
  [KanComplex X'] [KanComplex Y'] {n : ℕ} {A : Type v} {B : Type w}

/-- 同じ実同値の逆射を通じた全基点チャート。 -/
def DGBarCompactPiChart.ofEquivalence (c : DGBarCompactPiChart X n A)
    (e : QCatEquivalence X Y) : DGBarCompactPiChart Y n A where
  equiv y := (KanHomotopyGroup.equivOfPiIsomorphism n e.inv
    (HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence e.inv
      e.symm.isQCatEquivalence.isSimplicialHomotopyEquivalence) rfl).toEquiv.trans
        (c.equiv (e.inv.app _ y))
  of_transport p a b h := c.of_transport (p.map e.inv) _ _
    (dgBarCompactPiTransport_map n e.inv p h)

/-- 全比較の可逆正方形を、同じ逆データの正方形に変換する。 -/
def dgBarCompactInverseComparisonIso (e : QCatEquivalence X Y)
    (e' : QCatEquivalence X' Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : FunctorIso (f ≫ e'.hom) (e.hom ≫ g)) :
    FunctorIso (e.inv ≫ f) (g ≫ e'.inv) := by
  have h₁ : FunctorIso (e.inv ≫ f) ((e.inv ≫ f) ≫ (e'.hom ≫ e'.inv)) := by
    simpa only [Category.comp_id] using (e'.homInvIso.precomp (e.inv ≫ f)).symm
  have h₂ := (h.precomp e.inv).postcomp e'.inv
  have h₃ := e.invHomIso.postcomp (g ≫ e'.inv)
  simp only [Category.assoc, Category.id_comp] at h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃)

/-- 実辺の全空間比較に沿い、元の係数の自然性を native 側へ運ぶ。 -/
lemma dgBarCompactPiChart_naturality_of_comparison
    (c : DGBarCompactPiChart X n A) (c' : DGBarCompactPiChart X' n B)
    (e : QCatEquivalence X Y) (e' : QCatEquivalence X' Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (φ : A → B)
    (h : FunctorIso (f ≫ e'.hom) (e.hom ≫ g))
    (hf : ∀ x a, c'.equiv (f.app _ x) (dgBarCompactPiMap n f x a) = φ (c.equiv x a))
    (y : Y _⦋0⦌) (a : KanHomotopyGroup Y n y) :
    (c'.ofEquivalence e').equiv (g.app _ y) (dgBarCompactPiMap n g y a) =
      φ ((c.ofEquivalence e).equiv y a) := by
  have hi := c'.functorIso (dgBarCompactInverseComparisonIso e e' f g h) y a
  have hleft := DFunLike.congr_fun
    (KanHomotopyGroup.map_comp e.inv rfl f rfl rfl) a
  have hright := DFunLike.congr_fun
    (KanHomotopyGroup.map_comp g rfl e'.inv rfl rfl) a
  have he : (c'.ofEquivalence e').equiv (g.app _ y) (dgBarCompactPiMap n g y a) =
      c'.equiv ((e.inv ≫ f).app _ y)
        (dgBarCompactPiMap n (e.inv ≫ f) y a) := by
    dsimp only [DGBarCompactPiChart.ofEquivalence, Equiv.trans_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      KanHomotopyGroup.equivOfPiIsomorphism_apply]
    exact (congrArg (c'.equiv ((g ≫ e'.inv).app _ y)) hright.symm).trans hi.symm
  rw [he]
  have hf' : c'.equiv ((e.inv ≫ f).app _ y)
      (((KanHomotopyGroup.map f rfl).comp (KanHomotopyGroup.map e.inv rfl)) a) =
        φ ((c.ofEquivalence e).equiv y a) := by
    dsimp only [DGBarCompactPiChart.ofEquivalence, Equiv.trans_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      KanHomotopyGroup.equivOfPiIsomorphism_apply]
    exact hf (e.inv.app _ y) (dgBarCompactPiMap n e.inv y a)
  exact (congrArg (c'.equiv ((e.inv ≫ f).app _ y)) hleft).trans hf'

/-- 同じ実逆データによる連結成分チャート。 -/
def dgBarCompactPiZeroChart_ofEquivalence (α : SSet.π₀ X ≃ A)
    (e : QCatEquivalence X Y) : SSet.π₀ Y ≃ A :=
  (Equiv.ofBijective (SSet.mapπ₀ e.inv)
    e.symm.isQCatEquivalence.isSimplicialHomotopyEquivalence.mapPiZero_bijective).trans α

lemma dgBarCompactPiZeroChart_naturality_of_comparison
    (α : SSet.π₀ X ≃ A) (β : SSet.π₀ X' ≃ B)
    (e : QCatEquivalence X Y) (e' : QCatEquivalence X' Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (φ : A → B)
    (h : FunctorIso (f ≫ e'.hom) (e.hom ≫ g))
    (hf : ∀ a, β (SSet.mapπ₀ f a) = φ (α a)) (a : SSet.π₀ Y) :
    dgBarCompactPiZeroChart_ofEquivalence β e' (SSet.mapπ₀ g a) =
      φ (dgBarCompactPiZeroChart_ofEquivalence α e a) := by
  have hi := mapPiZero_eq_of_homotopy
    (FunctorIso.simplicialHomotopy (dgBarCompactInverseComparisonIso e e' f g h)) a
  rw [SSet.mapπ₀_comp_apply, SSet.mapπ₀_comp_apply] at hi
  exact (congrArg β hi.symm).trans (hf (SSet.mapπ₀ e.inv a))

end SerrePositivity.InfinityCategories
