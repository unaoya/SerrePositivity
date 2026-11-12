module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorCutTerm
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProductPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorElementHEq
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorCandidate
/-!
概要：全次元の tensor 候補の符号・切断項・有限和・全データは単射に沿う制限と可換である。
方針：符号を数える点対と powerset を像の添字へ全単射で移し、同じ実 cochain を比較する。
規約：HA 方程式を前提にしない生のデータの比較。使われ方：二入力 dg nerve の tensor 構成。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 同じ順序付き点対を数える交差符号は単射の像で変わらない。 -/
lemma dgNerveTensorCutSign_image {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hα : Function.Injective α) (I S : Finset (Fin (m + 1))) (a b : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.image α) (α a) (α b) (S.image α) := by
  have hs := α.monotone.strictMono_of_injective hα
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign
  apply congrArg (fun k : ℕ => (k : ℤ))
  apply Finset.card_bij (fun p _ => (α p.1, α p.2))
  · intro p hp
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    obtain ⟨hyI, hyS⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyb, hyI⟩ := Finset.mem_erase.mp hyI
    obtain ⟨hya, hyI⟩ := Finset.mem_erase.mp hyI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p.1, hx, rfl⟩, ?_⟩, hs hlt⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨fun h => hyb (hα h),
      Finset.mem_erase.mpr ⟨fun h => hya (hα h), Finset.mem_image.mpr ⟨p.2, hyI, rfl⟩⟩⟩, ?_⟩
    intro hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    exact hyS ((hα hzy) ▸ hz)
  · intro p _ q _ he
    exact Prod.ext (hα (congrArg Prod.fst he)) (hα (congrArg Prod.snd he))
  · rintro ⟨qx, qy⟩ hq
    obtain ⟨hq, hlt⟩ := Finset.mem_filter.mp hq
    obtain ⟨hxq, hyq⟩ := Finset.mem_product.mp hq
    obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hxq
    obtain ⟨hyq, hyS⟩ := Finset.mem_filter.mp hyq
    obtain ⟨hyb, hyq⟩ := Finset.mem_erase.mp hyq
    obtain ⟨hya, hyq⟩ := Finset.mem_erase.mp hyq
    obtain ⟨y, hyI, hyq⟩ := Finset.mem_image.mp hyq
    refine ⟨(x, y), ?_, Prod.ext hxq hyq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hx, ?_⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hyI⟩⟩, ?_⟩
      · intro h; change y = b at h; subst y; exact hyb hyq.symm
      · intro h; change y = a at h; subst y; exact hya hyq.symm
      · intro h; exact hyS (Finset.mem_image.mpr ⟨y, h, hyq⟩)
    · apply hs.lt_iff_lt.mp
      rwa [hxq, hyq]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ符号付き tensor 切断項は、単射の像と実 cochain 上で一致する。 -/
lemma dgNerveTensorCutTerm_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (S : Finset (Fin (m + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (m + 1))) a) (hb : IsGreatest (I : Set (Fin (m + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C (s.pullback α) (t.pullback α) I a b S k hk hI ha hb hc =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t (I.image α) (α a) (α b) (S.image α) k
        (by rw [Finset.card_image_of_injOn hα.injOn]; exact hk)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hα.injOn hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageLeast α I a ha)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageGreatest α I b hb) (by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          have h := hc x hx
          have hs := α.monotone.strictMono_of_injective hα
          exact ⟨Finset.mem_image.mpr ⟨x, h.1, rfl⟩, hs h.2.1, hs h.2.2⟩) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
  dsimp only
  rw [← dgNerveTensorCutSign_image α hα I S a b]
  congr 1
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C rfl rfl
    (by simp only [Finset.card_image_of_injOn hα.injOn])
    (by simp only [Finset.card_image_of_injOn hα.injOn]) rfl _ _ _ _ ?_ ?_ _ _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj s α (insert a (insert b S)) a b
      (-(S.card : ℤ)) _ _ _ _ hα.injOn]
    exact s.hom_heq_of_indices_degree (by simp only [Finset.image_insert]) rfl rfl
      (by simp only [Finset.card_image_of_injOn hα.injOn])
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_pullback_heq R C t α hα I a b S hI ha hb hc
open scoped BigOperators
/-- 全切断集合の同じ有限和は、単射の像の有限和と一致する。 -/
lemma dgNerveTensorHomCandidate_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (m + 1))) a) (hb : IsGreatest (I : Set (Fin (m + 1))) b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C (s.pullback α) (t.pullback α) I a b k hk hI ha hb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s t (I.image α) (α a) (α b) k
        (by rw [Finset.card_image_of_injOn hα.injOn]; exact hk)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hα.injOn hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageLeast α I a ha)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageGreatest α I b hb) := by
  classical
  let K := I.filter (fun j => a < j ∧ j < b)
  let K' := (I.image α).filter (fun j => α a < j ∧ j < α b)
  have hK : K.image α = K' := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hx, hax, hxb⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        (α.monotone.strictMono_of_injective hα) hax,
        (α.monotone.strictMono_of_injective hα) hxb⟩
    · intro hy
      obtain ⟨hy, hay, hyb⟩ := Finset.mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,
        (α.monotone.strictMono_of_injective hα).lt_iff_lt.mp hay,
        (α.monotone.strictMono_of_injective hα).lt_iff_lt.mp hyb⟩, rfl⟩
  let φ : K.powerset → K'.powerset := fun S => ⟨S.val.image α, by
    rw [← hK]
    apply Finset.mem_powerset.mpr
    exact Finset.image_mono α (Finset.mem_powerset.mp S.property)⟩
  have hi : Function.Injective φ := by
    intro S T hST
    apply Subtype.ext
    exact Finset.image_injective hα (congrArg Subtype.val hST)
  have he : Function.Surjective φ := by
    intro T
    have hT : T.val ∈ (K.image α).powerset := by rw [hK]; exact T.property
    rw [Finset.powerset_image] at hT
    obtain ⟨S, hS, hST⟩ := Finset.mem_image.mp hT
    exact ⟨⟨S, hS⟩, Subtype.ext hST⟩
  let e : K.powerset ≃ K'.powerset := Equiv.ofBijective φ ⟨hi, he⟩
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate
  apply Fintype.sum_equiv e
  intro S
  exact dgNerveTensorCutTerm_pullback R B C s t α hα I a b S.val k hk hI ha hb (by
    intro j hj
    exact Finset.mem_filter.mp (Finset.mem_powerset.mp S.property hj))
/-- 全次元の候補データは任意の単射に沿う入力の制限と可換である。 -/
lemma dgNerveTensorDataCandidate_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
    (s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α)
    (t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)) rfl
  apply heq_of_eq
  funext I a b k hI ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ α I a b k hI ha hb hk hα.injOn]
  have h := dgNerveTensorHomCandidate_pullback R B C s t α hα I a b k hk hI
    (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate] using! h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
