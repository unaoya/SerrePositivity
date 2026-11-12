module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrier

/-!
概要：全境界の条件と最後の部分複体内の充填から、同じ単体の全制限の条件を得る。
方針：非全射の制限は境界で、全射の制限は最後の頂点を保持することを使う。
規約：零次元は指定頂点の所属から直接与える。
使われ方：鎖を実現する空間の射影の境界持ち上げ。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X : SSet.{u}}
  (A : I → X.Subcomplex) (z : I → X _⦋0⦌)

/-- 全射な順序写像は最後の頂点を保持する。 -/
lemma simplexHom_last_of_surjective {m n : SimplexCategory} (α : m ⟶ n)
    (hα : Function.Surjective α.toOrderHom) :
    α.toOrderHom (Fin.last m.len) = Fin.last n.len := by
  obtain ⟨i, hi⟩ := hα (Fin.last n.len)
  apply le_antisymm (Fin.le_last _)
  exact hi ▸ α.toOrderHom.monotone (Fin.le_last i)

/-- 正次元の単体の全境界の条件は、最後の部分複体内の充填により全単体へ延びる。 -/
lemma terminalCarrierCondition_of_boundary {n : ℕ}
    {x : X _⦋n + 1⦌} {s : (nerve I) _⦋n + 1⦌}
    (hx : x ∈ (A (s.obj (Fin.last (n + 1)))).obj _)
    (hb : ∀ (m : SimplexCategory) (α : m ⟶ ⦋n + 1⦌),
      ¬ Function.Surjective α.toOrderHom →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (X.map α.op x) ((nerve I).map α.op s)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z x s := by
  constructor
  · intro m α
    by_cases hα : Function.Surjective α.toOrderHom
    · rw [simplexHom_last_of_surjective α hα]
      exact (A (s.obj (Fin.last (n + 1)))).map α.op hx
    · have h := (hb m α hα).1 m (𝟙 m)
      change X.map (𝟙 _) (X.map α.op x) ∈
        (A (s.obj (α.toOrderHom (Fin.last m.len)))).obj _ at h
      simpa only [CategoryTheory.Functor.map_id_apply] using h
  · intro i
    let α := SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ i
    have hα : ¬ Function.Surjective α.toOrderHom := by
      intro h
      have : Epi α := SimplexCategory.epi_iff_surjective.mpr h
      have hh := SimplexCategory.len_le_of_epi α
      change n + 1 ≤ 0 at hh
      omega
    have h := (hb ⦋0⦌ α hα).2 (0 : Fin 1)
    have he : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ :=
      Subsingleton.elim _ _
    rw [he] at h
    change X.map (𝟙 _) (X.map α.op x) = z (s.obj i) at h
    simpa only [CategoryTheory.Functor.map_id_apply] using h

/-- 指定頂点が部分複体に属すれば、零単体の全条件を満たす。 -/
lemma terminalCarrierCondition_zero (s : (nerve I) _⦋0⦌)
    (hz : z (s.obj 0) ∈ (A (s.obj 0)).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (z (s.obj 0)) s := by
  constructor
  · intro m α
    have hi : α.toOrderHom (Fin.last m.len) = 0 :=
      @Subsingleton.elim (Fin 1) inferInstance _ _
    rw [hi]
    exact (A (s.obj 0)).map α.op hz
  · intro i
    have hi : i = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
    subst i
    have he : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ :=
      Subsingleton.elim _ _
    rw [he]
    exact ConcreteCategory.congr_hom (X.map_id _) _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
