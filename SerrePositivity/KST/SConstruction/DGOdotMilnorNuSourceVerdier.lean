module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuVerdier
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceNullRectangle

/-!
概要：実始域比較長方形の外周を、同じ resolved 商と完備化を持つ列で認証する。
方針：実核比較の ν 同値から包含の同じ本質像を回収し、既存の核列を使用する。
規約：元の S 合成辺と同じ native 商・指定 c を保ち、局所化 API を新設しない。
使われ方：Sp の完備化付き接続口へ渡す外周列と指定商境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local notation "A" => dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)
local notation "T" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "a" => dgOdotMilnorSourceKernelInputMap R d
local notation "b" => dgOdotMilnorFlatKernelInputMap R d
local notation "i" => dgOdotMilnorFlatKernelExactMap R d
local notation "q" => dgOdotMilnorNuNativeProjection R d

/-- 概要：外周の同じ実 S 合成辺を固定 ν の包含射にする。
方針：元 cell 始域から核を経る厳密合成を使用する。
規約：ν の下で逆増大を選択しない。使われ方：外周列の実左射。 -/
abbrev dgOdotMilnorNuSourceInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (A) (T) := dgKInputNuMap R ((a) ≫ (b))

/-- 概要：元 S 合成辺の ν 像は同じ二つの完全射の合成そのもの。
方針：固定界面と実ラベル付き Perf 関手の合成保存を使用する。
規約：全関手の厳密等号。使われ方：外周の本質像と充満忠実性の照合。 -/
lemma dgOdotMilnorNuSourceInclusion_hom : (dgOdotMilnorNuSourceInclusion R d).hom =
    (dgOdotMilnorSourceKernelExactMap R d).hom ≫ (i).hom := by
  have h := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom
    ((presentedPerfectDGStableCategoryFunctor R).map_comp (a) (b))
  change (presentedPerfectDGExactMap R ((a) ≫ (b))).hom =
    (presentedPerfectDGExactMap R (a)).hom ≫ (presentedPerfectDGExactMap R (b)).hom at h
  rw [← dgKInputNuMap_eq R, ← dgKInputNuMap_eq R, ← dgKInputNuMap_eq R] at h
  exact h

/-- 概要：外周の実包含の本質像は同じ厚平坦核の ν 包含像に一致する。
方針：同じ核比較同値の逆と指定二胞体を使用する。
規約：retract 閉包を縮めない。使われ方：元の核・局所化証拠の再利用。 -/
lemma dgOdotMilnorNuSourceInclusion_image (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgOdotMilnorNuSourceInclusion R d) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (i) := by
  ext y
  let e := dgOdotMilnorSourceKernelNuEquivalence R d h
  constructor
  · rintro ⟨x, ⟨v⟩⟩
    refine ⟨e.hom.app (Opposite.op ⦋0⦌) x, ⟨?_⟩⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (((dgOdotMilnorSourceKernelExactMap R d).hom ≫ (i).hom).app _ x) y
    rw [← dgOdotMilnorNuSourceInclusion_hom]
    exact v
  · rintro ⟨x, ⟨v⟩⟩
    refine ⟨e.inv.app (Opposite.op ⦋0⦌) x, ⟨?_⟩⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((dgOdotMilnorNuSourceInclusion R d).hom.app _ _) y
    rw [dgOdotMilnorNuSourceInclusion_hom]
    exact ((e.invHomIso.app x).map (i).hom).trans v

/-- 概要：外周の同じ実包含と native resolved 商の Verdier 条件。
方針：核比較の同値・同じ本質像と検証済み核列の三欄を使用する。
規約：商射影も局所化辺族も変更しない。使われ方：外周列の具体的認証。 -/
lemma dgOdotMilnorNuSource_isVerdier (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgOdotMilnorNuSourceInclusion R d) (q) where
  fullyFaithful := by
    rw [dgOdotMilnorNuSourceInclusion_hom]
    exact (dgOdotMilnorSourceKernelNu_isQCatEquivalence R d h).isFullyFaithful.comp
      (dgOdotMilnorNuKernelInclusion_fullyFaithful R d h)
  kernel y := by
    rw [dgOdotMilnorNuSourceInclusion_image R d h]
    exact dgOdotMilnorNuKernel R d h y
  quotient := by
    rw [dgOdotMilnorNuSourceInclusion_image R d h]
    exact dgOdotMilnorNuKernelLocalization R d h

/-- 概要：実始域比較長方形の外周に対応する同じ未完備商の列。
方針：元 S 合成辺と検証済み native 商射影を保持する。
規約：完備化後の射を strict 局所化と扱わない。使われ方：外周の strict 商欄。 -/
def dgOdotMilnorNuSourceNativeSequence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u + 1} where
  left := A
  middle := T
  right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d
  inclusion := dgOdotMilnorNuSourceInclusion R d
  projection := q
  isVerdier := dgOdotMilnorNuSource_isVerdier R d h

/-- 概要：同じ外周列に D-21 の同じ指定完備化を接続する。
方針：実固定 ν 頂点の完備性と構成済み c・hc を使用する。
規約：元始域の回収には既存の増大屋根を併用する。使われ方：Sp の外周面証明書。 -/
def dgOdotMilnorNuSourcePerfectSequence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    PerfectVerdierSequence.{u + 1} where
  verdier := dgOdotMilnorNuSourceNativeSequence R d h
  left_complete := dgKInputStableValue_isIdempotentComplete R _
  middle_complete := dgKInputStableValue_isIdempotentComplete R _
  right := dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
  completion := dgOdotMilnorCompletion R d
  isCompletion := dgOdotMilnorCompletion_isIdempotentCompletion R d

/-- 概要：外周の完備化後の射影も元の固定 ν cell 商辺と全自然に比較する。
方針：右面と全く同じ商・完備化の比較を使用する。
規約：同じ指定関手同型。使われ方：Sp の外周の指定商境界。 -/
def dgOdotMilnorNuSourcePerfectProjectionComparison (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgOdotMilnorCellProjectionExactMap R d).hom
      (dgOdotMilnorNuSourcePerfectSequence R d h).projection.hom :=
  dgOdotMilnorNuPerfectProjectionComparison R d h

end SerrePositivity.KST.SConstruction
