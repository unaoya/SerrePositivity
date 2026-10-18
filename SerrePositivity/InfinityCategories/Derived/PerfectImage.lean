module
public import SerrePositivity.InfinityCategories.Derived.PerfectHomotopy
public import SerrePositivity.InfinityCategories.Derived.SemifreeResolution

/-! # h Perf の有限射影代表による像

概要：h Perf の複体ホモトピー圏での本質像は有界有限射影複体の像に一致する。
方針：一方は対象の完全モデル条件、他方は有限射影代表の semifree 解像度を使う。
規約：像は同型閉包を含めて比較する。使われ方：K 理論と既存の perfect 圏の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (S : Type u) [CommRing S]

/-- 概要：h Perf の通常の複体ホモトピー圏への比較。
方針：完全 dg 部分圏の H⁰ を semifree の H⁰ に含めて既存の比較を取る。
規約：導来圏の宇宙の選択を要しない。使われ方：有限射影代表との像の比較。 -/
def perfectComplexHomotopyInclusion : perfectInfinityHomotopyCategory S ⥤
    _root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ) :=
  (perfectInfinityH0Equivalence S).functor ⋙ perfectH0Inclusion S ⋙ semifreeHomotopyComparison S

/-- 概要：複体ホモトピー圏への比較は充満である。
方針：同値と二つの充満包含を合成する。
規約：全ての鎖写像のホモトピー類を含む。使われ方：本質像としての h Perf。 -/
instance perfectComplexHomotopyInclusion_full : (perfectComplexHomotopyInclusion S).Full := by
  dsimp [perfectComplexHomotopyInclusion, perfectH0Inclusion]
  infer_instance

/-- 概要：複体ホモトピー圏への比較は忠実である。
方針：同値と二つの忠実比較を合成する。
規約：ホモトピー類の等式を反映する。使われ方：充満部分圏としての同定。 -/
instance perfectComplexHomotopyInclusion_faithful :
    (perfectComplexHomotopyInclusion S).Faithful := by
  dsimp [perfectComplexHomotopyInclusion, perfectH0Inclusion]
  infer_instance

/-- 概要：h Perf の像は有界有限射影複体と同型なホモトピー圏の対象である。
方針：H⁰ の対象に付された完全モデル条件を取り出す。
規約：同型閉包で記述する。使われ方：本質像の片方向。 -/
lemma perfectComplexHomotopyInclusion_obj (X : perfectInfinityHomotopyCategory S) :
    (perfectHomotopyProperty S).isoClosure ((perfectComplexHomotopyInclusion S).obj X) := by
  let P : PerfectSemifree S := ForgetEnrichment.to (Complex S)
    ((perfectInfinityH0Equivalence S).functor.obj X).as
  exact P.property

/-- 概要：h Perf の本質像は有界有限射影複体のホモトピー圏での像の同型閉包に一致する。
方針：有限射影代表に semifree 解像度を取り、その擬同型をホモトピー同値にする。
規約：有界有限射影複体が semifree であるとは仮定しない。使われ方：h Perf の像の主定理。 -/
theorem perfectComplexHomotopyInclusion_essImage_iff
    (X : _root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ)) :
    (∃ Y : perfectInfinityHomotopyCategory S,
      Nonempty ((perfectComplexHomotopyInclusion S).obj Y ≅ X)) ↔
        (perfectHomotopyProperty S).isoClosure X := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact (perfectHomotopyProperty S).isoClosure.prop_of_iso e
      (perfectComplexHomotopyInclusion_obj S Y)
  · rintro ⟨Z, hZ, ⟨e⟩⟩
    obtain ⟨K, rfl⟩ := Z.quotient_obj_surjective
    have hK := (perfectHomotopyProperty_quotient S K).mp hZ
    obtain ⟨P, q, hP, _, hq⟩ := exists_complexSemifree_resolution S K
    have := complexSemifree_isKProjective S hP
    have := DifferentialGraded.strictlyPerfectComplex_isKProjective S K hK
    have : IsIso ((HomotopyCategory.quotient _ _).map q) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).2
        ((CochainComplex.IsKProjective.quasiIso_iff q).1 hq)
    let P' : PerfectSemifree S := ⟨⟨P, hP⟩,
      (complexPerfectModel_iff_quasiIso S P hP).2 ⟨K, hK, q, hq⟩⟩
    let Y := (toHomotopy S (PerfectSemifree S)).obj (ForgetEnrichment.of (Complex S) P')
    let G := perfectH0Inclusion S ⋙ semifreeHomotopyComparison S
    exact ⟨(perfectInfinityH0Equivalence S).inverse.obj Y,
      ⟨G.mapIso ((perfectInfinityH0Equivalence S).counitIso.app Y) ≪≫
        asIso ((HomotopyCategory.quotient _ _).map q) ≪≫ e.symm⟩⟩

end SerrePositivity.InfinityCategories
