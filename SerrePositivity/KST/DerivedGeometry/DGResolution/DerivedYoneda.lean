module

public import SerrePositivity.DifferentialGraded.Derived.RestrictionConservative
public import SerrePositivity.DifferentialGraded.Functor.HomIso
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology

/-!
# H⁰ から導来加群圏への代表加群による完全忠実な埋め込み

概要：一般の dg 圏の H⁰ を、実際の dg Yoneda と導来局所化で完全忠実に埋め込む。
方針：全 Hom の Yoneda 同型と代表加群のホモトピー射影性を使う。
規約：元の Hom の平坦性は要求しない。前三角化の本質的全射性は別問題。
使われ方：Drinfeld §2.4、KST D4・§10-7 の H⁰ と前三角化の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：実際の dg Yoneda 関手は全 Hom 複体で同型。
方針：代表加群に対する豊穣 Yoneda 同型の逆であることを使う。
規約：元の dg 圏の Hom に平坦性を課さない。
使われ方：Drinfeld §2.4、KST D4 の代表加群の完全忠実性。
-/
theorem yoneda_hom_isIso (x y : D) : IsIso ((dgYoneda A D).map x y) := by
  change IsIso (dgYonedaIso A x (representable A y)).inv
  infer_instance

/--
概要：実際の dg Yoneda 関手は全 Hom で準同型。
方針：証明済みの chain 同型から得る。
規約：本質的全射性は主張しない。
使われ方：Drinfeld §2.4、KST D4 の H⁰ 埋め込み。
-/
theorem yoneda_homQuasiIso : HomQuasiIso (dgYoneda A D) := by
  intro x y
  have := yoneda_hom_isIso A D x y
  infer_instance

/--
概要：H⁰ から導来加群圏への代表加群の関手は各 Hom で全単射。
方針：dg Yoneda の H⁰ 上の全単射と、射影的な代表加群からの局所化の全単射を合成する。
規約：導来関手は既存の実際の局所化を使う。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
theorem derivedYoneda_map_bijective (x y : HomotopyCategory A D) :
    Function.Bijective ((representableHomotopyToDerived A D).map (X := x) (Y := y)) := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  have hY := (dgYoneda A D).onHomotopy_map_bijective_of_homQuasiIso
    (yoneda_homQuasiIso A D) x y
  let P : ModuleCategory A D := (dgYoneda A D).onClosed.obj x
  have hP : moduleHomotopicallyProjective A D P :=
    representable_homotopicallyProjective A D (ForgetEnrichment.to (Complex A) x)
  have hL := moduleProjectiveLocalization_map_bijective A D hP
    ((dgYoneda A D).onHomotopy.obj ((toHomotopy A D).obj y))
  exact hL.comp hY

/--
概要：H⁰ から実際の導来加群圏への代表加群の関手は充満。
方針：各 Hom の全単射の全射性を使う。
規約：像が全ての有限 cell を含むことは別途証明する。
使われ方：Drinfeld §2.4、KST D4 の cone の代表可能性への入力。
-/
instance derivedYoneda_full : (representableHomotopyToDerived A D).Full where
  map_surjective {x y} := (derivedYoneda_map_bijective A D x y).2

/--
概要：H⁰ から実際の導来加群圏への代表加群の関手は忠実。
方針：各 Hom の全単射の単射性を使う。
規約：追加の平坦性条件は不要。
使われ方：Drinfeld §2.4、KST D4 の H⁰ 比較の射の一意性。
-/
instance derivedYoneda_faithful : (representableHomotopyToDerived A D).Faithful where
  map_injective {x y} := (derivedYoneda_map_bijective A D x y).1

end SerrePositivity.KST.DerivedGeometry.DGResolution
