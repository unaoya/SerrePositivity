module

public import SerrePositivity.KST.Spectra.FilteredPointedHomotopy
public import SerrePositivity.KST.Spectra.PointedMappingParameters

/-!
概要：有限な点つき源からの写像族と filtered colimit の比較。
方針：有限パラメータで uncurry し、基点条件を保つ相対因子分解を使う。
規約：源とパラメータの有限性だけを要求し、Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。loop と telescope の整合性。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ PointedSimplicialSet.{u}} {c : Cocone D}
  (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c))
  (A : PointedSimplicialSet.{u}) [A.right.Finite]

include hc in
/-- 概要：有限な源とパラメータからの点つき写像族は一つの段で実現できる。
方針：uncurry した族の基点包含に対して相対因子分解し、再び curry する。
規約：Kan 性も遷移射の単射性も不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。内部 Hom の filtered colimit 比較の全射性。 -/
theorem finite_basedHom_factorization {P : SSet.{u}} [P.Finite]
    (s : P ⟶ (PointedObject.basedHom A c.pt).right) :
    ∃ (j : J) (t : P ⟶ (PointedObject.basedHom A (D.obj j)).right),
      t ≫ (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A (c.ι.app j)).right = s := by
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  let : (𝟙_ SSet.{u} ⊗ P).Finite := finite_of_iso (λ_ P).symm
  let earlier := toUnit (𝟙_ SSet.{u} ⊗ P) ≫ (D.obj j).hom
  let body := MonoidalClosed.uncurry (s ≫ PointedObject.basedHomι A c.pt)
  have h : earlier ≫ (c.ι.app j).right = A.hom ▷ P ≫ body := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]
    simp only [earlier, Category.assoc, Under.w]
    rfl
  obtain ⟨k, v, q, hq, heq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.finite_relative_factorization hc (A.hom ▷ P) j earlier body h
  have hfixed : A.hom ▷ P ≫ q = toUnit (𝟙_ SSet.{u} ⊗ P) ≫ (D.obj k).hom := by
    rw [hq]
    change (toUnit _ ≫ (D.obj j).hom) ≫ (D.map v).right = _
    rw [Category.assoc, Under.w]
  refine ⟨k, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A (D.obj k) q hfixed, ?_⟩
  apply (cancel_mono (PointedObject.basedHomι A c.pt)).mp
  rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← MonoidalClosed.curry_natural_right]
  change q ≫ (c.ι.app k).right = body at heq
  rw [heq, MonoidalClosed.curry_uncurry]

include hc in
/-- 概要：有限パラメータの写像族が余極限で一致すれば後続段で一致する。
方針：uncurry した有限な源からの射の等式を有限表示性で移す。
規約：点つき Hom の等化子への包含後に比較する。
使われ方：Goerss–Jardine I §7、HTT A.3.3。内部 Hom の余極限比較の単射性。 -/
theorem finite_basedHom_eq_eventually {P : SSet.{u}} [P.Finite] (j : J)
    (s t : P ⟶ (PointedObject.basedHom A (D.obj j)).right)
    (h : s ≫ (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A (c.ι.app j)).right =
      t ≫ (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A (c.ι.app j)).right) :
    ∃ (k : J) (v : j ⟶ k),
      s ≫ (PointedObject.basedHomMap A (D.map v)).right =
        t ≫ (PointedObject.basedHomMap A (D.map v)).right := by
  have hu := congrArg (fun z : P ⟶ (PointedObject.basedHom A c.pt).right ↦
    MonoidalClosed.uncurry (z ≫ PointedObject.basedHomι A c.pt)) h
  simp only [Category.assoc, PointedObject.basedHomMap_ι] at hu
  simp only [← Category.assoc, MonoidalClosed.uncurry_natural_right] at hu
  obtain ⟨k, v, hv⟩ := Limits.exists_eq_of_preservesColimit_coyoneda_self hc
    (MonoidalClosed.uncurry (s ≫ PointedObject.basedHomι A (D.obj j)))
    (MonoidalClosed.uncurry (t ≫ PointedObject.basedHomι A (D.obj j))) hu
  refine ⟨k, v, ?_⟩
  apply (cancel_mono (PointedObject.basedHomι A (D.obj k))).mp
  apply MonoidalClosed.uncurry_injective
  simp only [Category.assoc, PointedObject.basedHomMap_ι]
  simp only [← Category.assoc, MonoidalClosed.uncurry_natural_right]
  exact hv

end

end SerrePositivity.KST.Spectra.PointedMapping
