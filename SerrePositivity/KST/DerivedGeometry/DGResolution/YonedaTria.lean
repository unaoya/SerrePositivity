module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.DerivedYoneda
public import SerrePositivity.DifferentialGraded.Verdier.Derived

/-!
概要：実際の導来 Yoneda を有限 cell の前三角化へ制限する。
方針：完全忠実性を制限し、有限 cell の代表可能性から本質的全射性を導く。
規約：H⁰ と tria は別の圏として扱い、同値は証明によって構成する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の dg 増強の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.DerivedGeometry.DGResolution
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：導来 Yoneda の各対象は実際の有限 cell の導来像に属する。
方針：閉零対象での計算同型と代表加群の有限 cell の構成を使う。
規約：対象の同一視ではなく証明済みの同型を通して渡す。
使われ方：Drinfeld §2.4、KST D4 の H⁰ 比較関手。
-/
theorem derivedYoneda_mem_tria (X : HomotopyCategory A D) :
    derivedFiniteCellOver A D Set.univ ((representableHomotopyToDerived A D).obj X) := by
  obtain ⟨X⟩ := X
  exact (derivedFiniteCellOver A D Set.univ).prop_of_iso
    (representableHomotopyToDerivedComputation A D X).symm
    ((moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCell_representable A D (ForgetEnrichment.to (Complex A) X)))

/--
概要：元の dg 圏の H⁰ から tria への実際の導来 Yoneda 関手。
方針：導来 Yoneda を有限 cell の充満部分圏へ制限する。
規約：retract による冪等完備化は加えない。
使われ方：Drinfeld §2.4、KST D4 の増強の比較。
-/
def yonedaToTria : HomotopyCategory A D ⥤ TriaCategory A D :=
  (derivedFiniteCellOver A D Set.univ).lift (representableHomotopyToDerived A D)
    (derivedYoneda_mem_tria A D)

/--
概要：H⁰ の対象の Yoneda 像は同じ対象の代表加群の導来像と同型。
方針：既存の導来 Yoneda の計算同型を充満部分圏へ持ち上げる。
規約：H⁰ の対象を選び直さない。
使われ方：Drinfeld §2.4・Thm 3.4、KST D4 の商への代表対象の移送。
-/
def yonedaToTria_objIso (X : HomotopyCategory A D) :
    (yonedaToTria A D).obj X ≅
      triaRepresentable A D (ForgetEnrichment.to (Complex A) X.as) := by
  obtain ⟨X⟩ := X
  exact (derivedFiniteCellOver A D Set.univ).isoMk
    (representableHomotopyToDerivedComputation A D X)

/--
概要：H⁰ から tria への Yoneda は充満。
方針：実際の導来 Yoneda の充満性を充満部分圏へ制限する。
規約：元の dg 圏に平坦性は要求しない。
使われ方：Drinfeld §2.4、KST D4 の前三角化の比較。
-/
instance yonedaToTria_full : (yonedaToTria A D).Full := by
  dsimp [yonedaToTria]
  infer_instance

/--
概要：H⁰ から tria への Yoneda は忠実。
方針：実際の導来 Yoneda の忠実性を充満部分圏へ制限する。
規約：元の H⁰ の射の等式を反映する。
使われ方：Drinfeld §2.4、KST D4 の前三角化の比較。
-/
instance yonedaToTria_faithful : (yonedaToTria A D).Faithful := by
  dsimp [yonedaToTria]
  infer_instance

/--
概要：有限 cell が実際の代表加群なら H⁰ から tria への Yoneda は本質的全射。
方針：有限 cell の導来像の表示に代表可能性の同型を合成する。
規約：この条件は複体の dg 圏では操作木の帰納によって別途証明する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の H⁰ と tria の同値。
-/
theorem yonedaToTria_essSurj_of_representable
    (h : ∀ M : ModuleCategory A D, moduleFiniteCell A D M →
      ∃ x : D, Nonempty (M ≅ ForgetEnrichment.of (Complex A) (representable A x))) :
    (yonedaToTria A D).EssSurj where
  mem_essImage X := by
    obtain ⟨M, hM, ⟨e⟩⟩ := X.property
    obtain ⟨x, ⟨ex⟩⟩ := h M hM
    refine ⟨(toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x), ⟨?_⟩⟩
    exact (derivedFiniteCellOver A D Set.univ).isoMk
      (representableHomotopyToDerivedComputation A D (ForgetEnrichment.of (Complex A) x) ≪≫
        (moduleToDerived A D).mapIso ex.symm ≪≫ e)

end SerrePositivity.KST.DerivedGeometry.DGResolution
