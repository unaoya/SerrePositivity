module
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents

/-!
概要：Hom が次数別単射の dg 関手に沿い、持ち上げた全成分の nerve 方程式を回収する。
方針：既知の像の単体の方程式を、微分・合成の保存と単射性で反映する。
規約：持ち上げる成分の存在や ε 整合性そのものは仮定から取り除かない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

/-- 像が既知の単体となる成分族は、単射な Hom を通じて元の nerve の単体となる。 -/
def dgNerveSimplexOfMappedData (F : DGFunctor R C D)
    (hinj : ∀ (x y : C) (k : ℤ), Function.Injective ((F.map x y).f k))
    {n : ℕ} (t : SimplexData R C n) (s : Simplex R D n)
    (h : s.toSimplexData = t.map F) : Simplex R C n := by
  rcases s with ⟨s, hs⟩
  change s = t.map F at h
  subst s
  refine ⟨t, ?_⟩
  intro I a b k hI ha hb hk
  apply hinj (t.obj a) (t.obj b) (k + 1)
  rw [map_differential, SimplexData.map_rhs]
  exact hs I a b k hI ha hb hk

/-- 方程式の回収では、選んだ頂点・全斉次成分を変更しない。 -/
lemma dgNerveSimplexOfMappedData_data (F : DGFunctor R C D)
    (hinj : ∀ (x y : C) (k : ℤ), Function.Injective ((F.map x y).f k))
    {n : ℕ} (t : SimplexData R C n) (s : Simplex R D n)
    (h : s.toSimplexData = t.map F) :
    (dgNerveSimplexOfMappedData F hinj t s h).toSimplexData = t := by
  rcases s with ⟨s, hs⟩
  change s = t.map F at h
  subst s
  rfl

/-- 持ち上げた単体の像は、もとの既知の単体に厳密一致する。 -/
lemma dgNerveSimplexOfMappedData_map (F : DGFunctor R C D)
    (hinj : ∀ (x y : C) (k : ℤ), Function.Injective ((F.map x y).f k))
    {n : ℕ} (t : SimplexData R C n) (s : Simplex R D n)
    (h : s.toSimplexData = t.map F) :
    (dgNerveSimplexOfMappedData F hinj t s h).map F = s := by
  apply Simplex.ext
  change (dgNerveSimplexOfMappedData F hinj t s h).toSimplexData.map F = _
  rw [dgNerveSimplexOfMappedData_data]
  exact h.symm

/-- 対象と全次数 Hom の単射性は、全ての nerve 単体の単射性を与える。 -/
lemma dgNerveSimplex_map_injective (F : DGFunctor R C D)
    (hobj : Function.Injective F.obj)
    (hinj : ∀ (x y : C) (k : ℤ), Function.Injective ((F.map x y).f k)) (n : ℕ) :
    Function.Injective (fun s : Simplex R C n => s.map F) := by
  intro s t h
  have ho : s.obj = t.obj := by
    funext a
    apply hobj
    exact congrArg (fun z : Simplex R D n => z.obj a) h
  rcases s with ⟨⟨so, sh⟩, se⟩
  rcases t with ⟨⟨tobj, th⟩, te⟩
  change so = tobj at ho
  subst tobj
  apply Simplex.ext
  apply SimplexData.ext (s := ⟨so, sh⟩) (t := ⟨so, th⟩) rfl
  apply heq_of_eq
  funext I a b k hI ha hb hk
  apply hinj (so a) (so b) k
  exact eq_of_heq (SimplexData.hom_heq_of_eq
    (congrArg Simplex.toSimplexData h) I a b k hI ha hb hk)

section MapLift
variable {C' D' : Type v} [DGCategory R C'] [DGCategory R D']

/-- 各単体に像の持ち上げが存在すれば、単射性により単体的自然性も自動的に揃う。 -/
def dgNerveMapLift (F : DGFunctor R C' D')
    (hobj : Function.Injective F.obj)
    (hinj : ∀ (x y : C') (k : ℤ), Function.Injective ((F.map x y).f k))
    {X : SSet.{max u v}} (f : X ⟶ dgNerve R D')
    (hlift : ∀ (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)),
      ∃ s : Simplex R C' n, s.map F = f.app (Opposite.op ⦋n⦌) x) :
    X ⟶ dgNerve R C' where
  app n := ↾fun x => Classical.choose (hlift n.unop.len x)
  naturality {a b} α := by
    ext x
    symm
    apply dgNerveSimplex_map_injective F hobj hinj b.unop.len
    have ht := Classical.choose_spec (hlift a.unop.len x)
    have hu := Classical.choose_spec (hlift b.unop.len (X.map α x))
    change ((dgNerve R C').map α (Classical.choose (hlift a.unop.len x))).map F = _
    calc
      _ = (dgNerve R D').map α
          ((Classical.choose (hlift a.unop.len x)).map F) :=
        ConcreteCategory.congr_hom ((dgNerve.map F).naturality α) (Classical.choose (hlift a.unop.len x))
      _ = (dgNerve R D').map α (f.app a x) := congrArg _ ht
      _ = f.app b (X.map α x) := (ConcreteCategory.congr_hom (f.naturality α) x).symm
      _ = _ := hu.symm

/-- 選んだ全単体の持ち上げは、元の単体的写像を厳密に因子化する。 -/
lemma dgNerveMapLift_map (F : DGFunctor R C' D')
    (hobj : Function.Injective F.obj)
    (hinj : ∀ (x y : C') (k : ℤ), Function.Injective ((F.map x y).f k))
    {X : SSet.{max u v}} (f : X ⟶ dgNerve R D')
    (hlift : ∀ (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)),
      ∃ s : Simplex R C' n, s.map F = f.app (Opposite.op ⦋n⦌) x) :
    dgNerveMapLift F hobj hinj f hlift ≫ dgNerve.map F = f := by
  ext n x
  exact Classical.choose_spec (hlift n.unop.len x)

end MapLift

end SerrePositivity.InfinityCategories
