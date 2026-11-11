module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeKProjective
public import SerrePositivity.DifferentialGraded.Perfect.Ring.FiniteProjectiveComparison
public import SerrePositivity.PerfectComplex.BiproductPerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # 完全複体のホモトピー代表

概要：有界有限射影複体とホモトピー同値な複体のクラスを扱う。
方針：既存の strictlyPerfectComplex のホモトピー圏での同型閉包を取る。
規約：semifree 複体では有界有限射影複体への擬同型の存在と同値。
使われ方：Perf(S) の対象条件と演算による閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject
variable (S : Type u) [CommRing S]

/-- 概要：有界有限射影複体を代表とするホモトピー型。
方針：既存のホモトピー圏上の性質の同型閉包を取る。
規約：零ホモトピックな余分な項も許す。使われ方：完全な semifree 複体の判定。 -/
def complexPerfectModel (P : Complex S) : Prop :=
  (perfectHomotopyProperty S).isoClosure ((HomotopyCategory.quotient _ _).obj P)

/-- 概要：完全モデル条件は有界有限射影代表とのホモトピー圏での同型である。
方針：同型閉包の対象を複体の代表に戻す。
規約：複体自体の同型を要求しない。使われ方：擬同型による記述との比較。 -/
lemma complexPerfectModel_iff (P : Complex S) :
    complexPerfectModel S P ↔ ∃ K : Complex S, strictlyPerfectComplex S K ∧
      Nonempty ((HomotopyCategory.quotient _ _).obj P ≅
        (HomotopyCategory.quotient _ _).obj K) := by
  constructor
  · rintro ⟨X, hX, e⟩
    obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
    exact ⟨K, (perfectHomotopyProperty_quotient S K).mp hX, e⟩
  · rintro ⟨K, hK, e⟩
    exact ⟨_, (perfectHomotopyProperty_quotient S K).mpr hK, e⟩

/-- 概要：semifree 複体の完全性は有界有限射影複体への擬同型の存在で判定できる。
方針：K 射影性によって擬同型とホモトピー同値を同一視する。
規約：可換環以外の仮定なし。使われ方：Perf(S) の対象条件の公開形。 -/
theorem complexPerfectModel_iff_quasiIso (P : Complex S) (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) :
    complexPerfectModel S P ↔ ∃ K : Complex S, strictlyPerfectComplex S K ∧
      ∃ q : P ⟶ K, QuasiIso q := by
  rw [complexPerfectModel_iff]
  constructor
  · rintro ⟨K, hK, ⟨e⟩⟩
    obtain ⟨q, hq⟩ := (HomotopyCategory.quotient _ _).map_surjective e.hom
    have : IsIso ((HomotopyCategory.quotient _ _).map q) := hq ▸ e.isIso_hom
    exact ⟨K, hK, q, homotopyEquivalences_le_quasiIso _ _ _
      ((HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).mp inferInstance)⟩
  · rintro ⟨K, hK, q, hq⟩
    have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S hP
    have := DifferentialGraded.strictlyPerfectComplex_isKProjective S K hK
    have : IsIso ((HomotopyCategory.quotient _ _).map q) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).mpr
        ((CochainComplex.IsKProjective.quasiIso_iff q).mp hq)
    exact ⟨K, hK, ⟨asIso ((HomotopyCategory.quotient _ _).map q)⟩⟩

/-- 概要：有界有限射影複体は完全モデルである。
方針：同型閉包への標準包含を使う。
規約：恒等のホモトピー型。使われ方：零対象と有限射影加群の入力。 -/
lemma complexPerfectModel_of_strict {P : Complex S} (hP : strictlyPerfectComplex S P) :
    complexPerfectModel S P :=
  (perfectHomotopyProperty S).le_isoClosure _ ((perfectHomotopyProperty_quotient S P).mpr hP)

/-- 概要：零複体は完全モデルである。
方針：零複体の有界有限射影性を使う。
規約：任意の可換環。使われ方：Perf(S) の零対象。 -/
lemma complexPerfectModel_zero : complexPerfectModel S (0 : Complex S) :=
  complexPerfectModel_of_strict S strictlyPerfectComplex_zero

/-- 概要：完全モデル条件はホモトピー圏での同型で保たれる。
方針：同型閉包の不変性を使う。
規約：真の複体同型も含む。使われ方：比較射による完全性の転送。 -/
lemma complexPerfectModel_of_homotopyIso {P Q : Complex S}
    (e : (HomotopyCategory.quotient _ _).obj P ≅ (HomotopyCategory.quotient _ _).obj Q)
    (hP : complexPerfectModel S P) : complexPerfectModel S Q :=
  (perfectHomotopyProperty S).isoClosure.prop_of_iso e hP

/-- 概要：整数シフトは完全モデルを保つ。
方針：ホモトピー圏のシフトとの比較と同型閉包のシフト閉性を使う。
規約：全整数次数。使われ方：Perf(S) のシフト閉性。 -/
lemma complexPerfectModel_shift {P : Complex S} (hP : complexPerfectModel S P) (n : ℤ) :
    complexPerfectModel S (P⟦n⟧) := by
  change (perfectHomotopyProperty S).isoClosure _
  rw [← HomotopyCategory.shift_quotient_obj]
  exact (perfectHomotopyProperty S).isoClosure.le_shift n _ hP

/-- 概要：完全モデル間の射の写像錐は完全モデルである。
方針：同型閉包の三角閉性を写像錐の distinguished triangle に適用する。
規約：任意の鎖写像。使われ方：Perf(S) の cone 閉性。 -/
lemma complexPerfectModel_mappingCone {P Q : Complex S} (f : P ⟶ Q)
    (hP : complexPerfectModel S P) (hQ : complexPerfectModel S Q) :
    complexPerfectModel S (CochainComplex.mappingCone f) := by
  exact (perfectHomotopyProperty S).isoClosure.ext_of_isTriangulatedClosed₃
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f) hP hQ

/-- 概要：有限直和は完全モデルを保つ。
方針：加法的なホモトピー商が有限積を保つことと三角部分圏の有限積閉性を使う。
規約：任意の有限添字集合。使われ方：Perf(S) の有限直和閉性。 -/
lemma complexPerfectModel_finiteBiproduct {I : Type v} [Finite I]
    (P : I → Complex S) (hP : ∀ i, complexPerfectModel S (P i)) :
    complexPerfectModel S (⨁ P) := by
  exact (perfectHomotopyProperty S).isoClosure.prop_of_isLimit
    (isLimitOfPreserves (HomotopyCategory.quotient _ _) (biproduct.isLimit P))
    (fun i => hP i.as)

/-- 概要：二項直和は完全モデルを保つ。
方針：ホモトピー商での二項積の極限錐を使う。
規約：直和の順序は保持する。使われ方：標準 fiber の始域。 -/
lemma complexPerfectModel_binaryBiproduct {P Q : Complex S}
    (hP : complexPerfectModel S P) (hQ : complexPerfectModel S Q) :
    complexPerfectModel S (P ⊞ Q) := by
  apply (perfectHomotopyProperty S).isoClosure.prop_of_isLimit
    (isLimitOfPreserves (HomotopyCategory.quotient _ _) (BinaryBiproduct.isLimit P Q))
  rintro ⟨_ | _⟩
  · exact hP
  · exact hQ

/-- 概要：完全モデル間の射の fiber は完全モデルである。
方針：写像錐と −1 シフトの閉性を合成する。
規約：fiber の既存の符号規約。使われ方：Perf(S) の fiber 閉性。 -/
lemma complexPerfectModel_fiber {P Q : Complex S} (f : P ⟶ Q)
    (hP : complexPerfectModel S P) (hQ : complexPerfectModel S Q) :
    complexPerfectModel S ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧) :=
  complexPerfectModel_shift S (complexPerfectModel_mappingCone S f hP hQ) (-1)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
