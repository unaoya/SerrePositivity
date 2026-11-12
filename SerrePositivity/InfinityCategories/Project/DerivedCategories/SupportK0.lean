module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportBaseChangeComparison
public import SerrePositivity.KTheory.K0Localization

/-! # 台つき導来 ∞ 圏と既存 K₀ 局所化

概要：h Perf_Z の有限射影代表の K₀ 類は既存の局所化写像と整合する。
方針：台つき比較同値で既存の閉集合版へ送り、D5c の底変更比較を用いる。
規約：K₀ の右完全性の Noether・有限射影解像度仮定を保持する。
使われ方：L4 の T2 と論文 (3.6) の台の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：h Perf_Z の対象を既存の閉集合版 K₀ の類に送る。
方針：比較同値で有限射影代表を取りその類を取る。
規約：既存の K₀WithSupport を用いる。使われ方：局所化の類の比較。 -/
def perfectSupportK0Class (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S Z) : K0WithSupport Z :=
  K0WithSupport.mk Z ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.obj X)

/-- 概要：台つき比較で同型な対象は同じ K₀ 類を持つ。
方針：比較関手で同型を送る。
規約：対象の選択に依存しない。使われ方：有限射影代表による計算。 -/
lemma perfectSupportK0Class_iso {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S Z} (e : X ≅ Y) :
    perfectSupportK0Class S Z X = perfectSupportK0Class S Z Y :=
  TriangulatedK0.mk_iso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.mapIso e)

/-- 概要：既存の台つき有限射影対象の類は h Perf_Z の対象から得られる。
方針：比較同値の余単位を用いる。
規約：K₀ の生成元についての主張。使われ方：既存の局所化列の入力の同定。 -/
lemma perfectSupportK0Class_representative (Y : SupportedPerfectHomotopyOn Z) :
    perfectSupportK0Class S Z ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).inverse.obj Y) =
      K0WithSupport.mk Z Y :=
  TriangulatedK0.mk_iso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).counitIso.app Y)

variable {T : Type u} [CommRing T]

/-- 概要：既存 K₀ の底変更は h Perf_Z の代表に通常の底変更を施した類である。
方針：既存の map_mk を適用する。代表のホモトピー型は perfectSupportBaseChangeIso で D5c と一致。
規約：任意の環準同型。使われ方：D5c と既存の K₀ 写像の整合。 -/
lemma perfectSupportK0Class_baseChange (f : S →+* T)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S Z) :
    K0WithSupport.map f Z (supportPullback f Z) le_rfl (perfectSupportK0Class S Z X) =
      K0WithSupport.mk _ ((closedSupportChangeRing f Z (supportPullback f Z) le_rfl).obj
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.obj X)) :=
  K0WithSupport.map_mk ..

/-- 概要：D5c の局所化で零になる頂点の有限射影代表も、底変更後に零対象となる。
方針：底変更比較同型を通じて周囲の零性を充満忠実包含で反映する。
規約：対象の台は任意。使われ方：局所化の核の K₀ 類。 -/
lemma perfectSupportBaseChange_isZero (f : S →+* T)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌)
    (hx : IsZero (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f).app _ x.val⟩ :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory T)) :
    IsZero ((closedSupportChangeRing f Z (supportPullback f Z) le_rfl).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.obj ⟨x⟩)) := by
  let F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence T).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison T
  have hz : IsZero (F.obj ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex T⟩) :=
    (HomotopyCategory.quotient _ _).map_isZero (isZero_zero (Complex T))
  have hq : IsZero (F.obj ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f).app _ x.val⟩) :=
    hz.of_iso (F.mapIso (hx.iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex_isZero T)))
  let G := supportedPerfectOnInclusion (supportPullback f Z) ⋙
    SerrePositivity.perfectHomotopyInclusion T
  exact IsZero.of_full_of_faithful_of_isZero G _
    (hq.of_iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportBaseChangeIso S Z f x))

variable [Algebra S T]

/-- 概要：Perf_{V(a)} の K₀ 類は既存の主開局所化写像で零になる。
方針：一般の底変更核の判定、D5c 比較、零対象の K₀ 類を使う。
規約：この零化に Noether 条件は不要。使われ方：L4 の T2 の支持部分の零化。 -/
lemma perfectSupportK0Class_localize_zero (a : S) [IsLocalization.Away a T]
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S (supportZeroLocus (Ideal.span ({a} : Set S)))) _⦋0⦌) :
    K0WithSupport.localize (S := T) (Submonoid.powers a) _
      (perfectSupportK0Class S _ ⟨x⟩) = 0 := by
  rw [K0WithSupport.localize, perfectSupportK0Class_baseChange]
  exact TriangulatedK0.mk_of_isZero _ (perfectSupportBaseChange_isZero S _ (algebraMap S T) x
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory_baseChange_zero (T := T) a x))

/-- 概要：有限自由版 K0Supported からの既存写像は同じ幾何学的台の K₀ へ入る。
方針：既存の比較写像を公開する。
規約：任意の可換環では写像。使われ方：古典的な有限自由の表示との比較。 -/
abbrev supportedFreeK0Comparison {e : ℕ} (z : Fin e → S) := freeToClosedSupportK0 z

/-- 概要：局所環では有限自由版 K0Supported と幾何学的台の K₀ は同型である。
方針：既存の有限自由・有限射影比較を使う。
規約：局所環仮定を保持する。使われ方：論文 (3.6) の既存 K₀ 表示。 -/
abbrev supportedFreeK0Equivalence [IsLocalRing S] {e : ℕ} (z : Fin e → S) :=
  freeClosedSupportK0Equiv z

/-- 概要：既存の K₀ 主開局所化列の核は、閉部分の台を拡大した像である。
方針：既存の局所化定理を、この台つき表示の下で使う。
規約：Noether・有限射影解像度の仮定を保持する。使われ方：L4 の局所化の h レベル整合。 -/
lemma supportedK0_localization_kernel [IsNoetherianRing S] [IsNoetherianRing T]
    [HasFiniteProjectiveResolutions S] [HasFiniteProjectiveResolutions T]
    (a : S) [IsLocalization.Away a T] :
    (K0WithSupport.localize (S := T) (Submonoid.powers a) Z).ker =
      (K0WithSupport.enlarge
        (show Z ⊓ supportZeroLocus (Ideal.span ({a} : Set S)) ≤ Z from inf_le_left)).range :=
  K0WithSupport.localize_away_kernel_range (S := T) Z a

/-- 概要：既存の K₀ 主開局所化写像は全射である。
方針：既存の局所化全射性を同じ支持条件で適用する。
規約：Noether・有限射影解像度仮定を保持する。使われ方：局所化列の右完全性。 -/
lemma supportedK0_localization_surjective [IsNoetherianRing S] [IsNoetherianRing T]
    [HasFiniteProjectiveResolutions S] [HasFiniteProjectiveResolutions T]
    (a : S) [IsLocalization.Away a T] :
    Function.Surjective (K0WithSupport.localize (S := T) (Submonoid.powers a) Z) :=
  K0WithSupport.localize_surjective (S := T) (Submonoid.powers a) Z

end SerrePositivity.InfinityCategories.Project.DerivedCategories
