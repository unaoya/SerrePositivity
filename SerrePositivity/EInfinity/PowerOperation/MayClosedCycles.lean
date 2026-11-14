module

public import SerrePositivity.EInfinity.PowerOperation.MayDValues

/-!
# May の値を閉元の加群として保持する

May, Definitions 2.1・2.2 の閉性の前段。全整数次数で実際の微分の kernel を使い、
次数の等式による移送と全厳密射での自然性を同じ元について保持する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k]

/-- 元の整数次数の閉元の加群。 -/
abbrev MayClosed (K : Complex k) (i : ℤ) := LinearMap.ker (K.d i (i + 1)).hom

/-- 同じ次数の二つの式の間の指定移送。 -/
def mayClosedIndex (K : Complex k) {i j : ℤ} (h : i = j) :
    MayClosed K i ≃ₗ[k] MayClosed K j := by
  subst j
  exact LinearEquiv.refl _ _

/-- 元の複体射を閉元へ制限する。 -/
def mayClosedMap {K L : Complex k} (f : K ⟶ L) (i : ℤ) :
    MayClosed K i →ₗ[k] MayClosed L i where
  toFun x := ⟨f.f i x.val, by
    change L.d i (i + 1) (f.f i x.val) = 0
    have h := congrArg (fun g => g.hom x.val) (f.comm i (i + 1))
    change L.d i (i + 1) (f.f i x.val) = f.f (i + 1) (K.d i (i + 1) x.val) at h
    have hx : K.d i (i + 1) x.val = 0 := x.property
    rw [hx] at h
    exact h.trans (f.f (i + 1)).hom.map_zero⟩
  map_add' x y := by apply Subtype.ext; exact (f.f i).hom.map_add _ _
  map_smul' r x := by apply Subtype.ext; exact (f.f i).hom.map_smul r _

lemma mayClosedMap_comp {K L M : Complex k} (f : K ⟶ L) (g : L ⟶ M)
    (i : ℤ) (a : MayClosed K i) :
    mayClosedMap (f ≫ g) i a = mayClosedMap g i (mayClosedMap f i a) := by
  apply Subtype.ext
  rfl

lemma mayClosedMap_index {K L : Complex k} (f : K ⟶ L) {i j : ℤ} (h : i = j)
    (x : MayClosed K i) :
    mayClosedMap f j (mayClosedIndex K h x) = mayClosedIndex L h (mayClosedMap f i x) := by
  subst j
  rfl

variable (X : (operad k).Algebra) (p : ℕ) [NeZero p] [Fact p.Prime] [CharP k p]

/-- 指定 D_s の値を、実際の kernel の元として保持する。 -/
def mayDClosed (s : ℕ) (q : ℤ) (a : MayClosed X.carrier q) :
    MayClosed X.carrier (-(s : ℤ) + mayRepeatedDegree q p) :=
  ⟨mayDValue X p s q a.val, mayDValue_cycle X p s q a.val a.property⟩

lemma mayDClosed_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (s : ℕ) (q : ℤ) (a : MayClosed X.carrier q) :
    mayClosedMap f.hom (-(s : ℤ) + mayRepeatedDegree q p) (mayDClosed X p s q a) =
      mayDClosed Y p s q (mayClosedMap f.hom q a) := by
  apply Subtype.ext
  exact mayDValue_naturality X p f s q a.val

end SerrePositivity.EInfinity.PowerOperation
