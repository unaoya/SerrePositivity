module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.ExtensionDomain
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOutsideSimplices

/-!
概要：twisted arrow の延長領域外の非退化単体の pairing を構成する。
方針：頂点集合の全単射を領域外へ制限し、有限集合の挿入・削除の対を移す。
規約：正則性と inner 条件は別に証明する。
使われ方：射影の left fibration 性のための inner horn 接合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 領域外の非退化単体の頂点集合も領域外にある。 -/
lemma twistedArrowNondegenerate_mem_iff_support {n : ℕ} (i : Fin (n + 1))
    (s : (Δ[n + n + 1] : SSet.{u}).N) :
    s.simplex ∈ (twistedArrowExtensionDomain n i).obj (Opposite.op ⦋s.dim⦌) ↔
      TwistedArrowSupportInDomain i (stdSimplexNondegenerateSupport s) := by
  rw [stdSimplexNondegenerateSupport_eq_image]
  exact mem_twistedArrowExtensionDomain_iff_support i s.simplex

/-- 延長領域外の非退化単体と領域外の有限頂点集合の全単射。 -/
def twistedArrowOutsideSimplexEquiv {n : ℕ} (i : Fin (n + 1)) :
    (twistedArrowExtensionDomain.{u} n i).N ≃
      {S : Finset (Fin (n + n + 1 + 1)) // ¬ TwistedArrowSupportInDomain i S} :=
  Equiv.ofBijective
    (fun s ↦ ⟨stdSimplexNondegenerateSupport s.toN, fun h ↦
      s.notMem ((twistedArrowNondegenerate_mem_iff_support i s.toN).mpr h)⟩) (by
      constructor
      · intro s t h
        apply (Subcomplex.N.ext_iff s t).mpr
        exact stdSimplexNondegenerateSupport_injective _ (congrArg Subtype.val h)
      · intro S
        obtain ⟨⟨a, ha, _⟩, _, _⟩ := (not_twistedArrowSupportInDomain_iff i S.val).mp S.property
        let x := (stdSimplexNondegenerateSupportEquiv.{u} (n + n + 1)).symm
          ⟨S.val, ⟨a, ha⟩⟩
        have hx : stdSimplexNondegenerateSupport x = S.val :=
          congrArg Subtype.val ((stdSimplexNondegenerateSupportEquiv (n + n + 1)).apply_symm_apply
            ⟨S.val, ⟨a, ha⟩⟩)
        have hn : x.simplex ∉ (twistedArrowExtensionDomain n i).obj (Opposite.op ⦋x.dim⦌) := by
          rw [twistedArrowNondegenerate_mem_iff_support, hx]
          exact S.property
        refine ⟨Subcomplex.N.mk' x hn, ?_⟩
        exact Subtype.ext hx)

/-- 挿入点を含む領域外の非退化単体。 -/
def twistedArrowUpperSimplices {n : ℕ} (i : Fin (n + 1)) :
    Set (twistedArrowExtensionDomain.{u} n i).N := fun s ↦
  twistedArrowSupportPivot i (stdSimplexNondegenerateSupport s.toN) ∈
    stdSimplexNondegenerateSupport s.toN

/-- 挿入点を欠く領域外の非退化単体。 -/
def twistedArrowLowerSimplices {n : ℕ} (i : Fin (n + 1)) :
    Set (twistedArrowExtensionDomain.{u} n i).N := fun s ↦
  twistedArrowSupportPivot i (stdSimplexNondegenerateSupport s.toN) ∉
    stdSimplexNondegenerateSupport s.toN

/-- 大きい方の単体と、挿入点を含む頂点集合の全単射。 -/
def twistedArrowUpperSimplexEquiv {n : ℕ} (i : Fin (n + 1)) :
    {s // s ∈ twistedArrowUpperSimplices.{u} i} ≃
      {S : Finset (Fin (n + n + 1 + 1)) //
        ¬ TwistedArrowSupportInDomain i S ∧ twistedArrowSupportPivot i S ∈ S} :=
  ((twistedArrowOutsideSimplexEquiv i).subtypeEquiv
    (p := fun s ↦ s ∈ twistedArrowUpperSimplices i)
    (q := fun S ↦ twistedArrowSupportPivot i S.val ∈ S.val) (fun _ ↦ Iff.rfl)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun S ↦ twistedArrowSupportPivot i S ∈ S))

/-- 小さい方の単体と、挿入点を欠く頂点集合の全単射。 -/
def twistedArrowLowerSimplexEquiv {n : ℕ} (i : Fin (n + 1)) :
    {s // s ∈ twistedArrowLowerSimplices.{u} i} ≃
      {S : Finset (Fin (n + n + 1 + 1)) //
        ¬ TwistedArrowSupportInDomain i S ∧ twistedArrowSupportPivot i S ∉ S} :=
  ((twistedArrowOutsideSimplexEquiv i).subtypeEquiv
    (p := fun s ↦ s ∈ twistedArrowLowerSimplices i)
    (q := fun S ↦ twistedArrowSupportPivot i S.val ∉ S.val) (fun _ ↦ Iff.rfl)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun S ↦ twistedArrowSupportPivot i S ∉ S))

/-- 左ホーンの延長領域外の非退化単体の pairing。 -/
def twistedArrowExtensionPairing {n : ℕ} (i : Fin (n + 1)) (hi : i < Fin.last n) :
    (twistedArrowExtensionDomain.{u} n i).Pairing where
  I := twistedArrowUpperSimplices i
  II := twistedArrowLowerSimplices i
  inter := by
    ext s
    change (_ ∧ ¬ _) ↔ False
    tauto
  union := by
    classical
    ext s
    change (_ ∨ ¬ _) ↔ True
    tauto
  p := (twistedArrowLowerSimplexEquiv i).trans
    ((twistedArrowSupportPairEquiv i hi).trans (twistedArrowUpperSimplexEquiv i).symm)

/-- pairing の大きい方の頂点集合は、小さい方へ選んだ内部点を挿入したもの。 -/
lemma twistedArrowExtensionPairing_support {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s : (twistedArrowExtensionPairing.{u} i hi).II) :
    stdSimplexNondegenerateSupport ((twistedArrowExtensionPairing i hi).p s).val.toN =
      insert (twistedArrowSupportPivot i (stdSimplexNondegenerateSupport s.val.toN))
        (stdSimplexNondegenerateSupport s.val.toN) := by
  have h := (twistedArrowUpperSimplexEquiv i).apply_symm_apply
    ((twistedArrowSupportPairEquiv i hi) (twistedArrowLowerSimplexEquiv i s))
  exact congrArg Subtype.val h

end SerrePositivity.InfinityCategories
