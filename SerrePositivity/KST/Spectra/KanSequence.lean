module

public import SerrePositivity.KST.Spectra.OmegaSpectrum
public import SerrePositivity.KST.Spectra.PointedFactorization

/-!
概要：構造射の単射性をまだ要求しない点つき Kan 複体のスペクトル列。
方針：各段と suspension 構造射を持つ列を、完成した Ω スペクトルから分ける。
規約：Ω 条件も単射性も、この構造の入力には含めない。
使われ方：BF 1978 §2、HTT A.3.3。置換前の列と厳密な比較射。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

/-- 概要：点つき Kan 複体と suspension 構造射の列。
方針：段ごとの Kan 性を束ねた既存の PointedKanComplex を使う。
規約：構造射は任意の点つき射。
使われ方：BF 1978 §2、HTT A.3.3。cofibrant 置換前の対象。 -/
structure KanSequence where
  /-- 概要：列の各段。
  方針：点つき Kan 複体を使う。
  規約：自然数で添字付ける。
  使われ方：BF 1978 §2。 -/
  level : ℕ → PointedKanComplex.{u}
  /-- 概要：列の suspension 構造射。
  方針：円との smash からの点つき射で与える。
  規約：単射性をまだ要求しない。
  使われ方：BF 1978 §2。 -/
  sigma : ∀ n, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (level n).space ⟶ (level (n + 1)).space

namespace KanSequence

/-- 概要：列の Ω 条件。
方針：随伴構造射が全基点で π_* 同型であることを要求する。
規約：完成した Ω スペクトルと同じ条件であり、厳密同型は要求しない。
使われ方：BF 1978 §2、HA §1.4.2。置換前後の fibrant 条件。 -/
def OmegaCondition (X : KanSequence.{u}) : Prop :=
  ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space) (X.sigma n)).right

/-- 概要：Kan 列の厳密な比較射。
方針：各段の点つき射と構造射との可換条件を持たせる。
規約：ホモトピー可換ではなく厳密可換。
使われ方：BF 1978 §2。置換から元の列への射。 -/
structure Hom (X Y : KanSequence.{u}) where
  /-- 概要：各段の射。
  方針：点つき射で与える。
  規約：同じ段の間の射。
  使われ方：BF 1978 §2。 -/
  app : ∀ n, (X.level n).space ⟶ (Y.level n).space
  /-- 概要：構造射との可換性。
  方針：suspension の射への作用を使う。
  規約：各段で厳密な等式。
  使われ方：BF 1978 §2。 -/
  comm : ∀ n, PointedSimplicialSet.circle.{u} ◁ app n ≫ Y.sigma n =
    X.sigma n ≫ app (n + 1)

/-- 概要：Kan 列の厳密な射の合成。
方針：各段の射を合成し、二つの構造射の可換式をつなぐ。
規約：段ごとの通常の合成。
使われ方：BF 1978 §2。置換した fiber から全空間への比較。 -/
def Hom.comp {X Y Z : KanSequence.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  app n := f.app n ≫ g.app n
  comm n := by
    rw [whiskerLeft_comp, Category.assoc, g.comm n, ← Category.assoc,
      f.comm n, Category.assoc]

/-- 概要：単射な構造射と Ω 条件を持つ Kan 列を本レーンの Ω スペクトルへ束ねる。
方針：構成済みの各データと証明をそのまま移す。
規約：この束ね直し自体は新しい条件を証明しない。
使われ方：BF 1978 §2、HA §1.4.2。置換の最終出力。 -/
def toOmegaSpectrum (X : KanSequence.{u}) (hmono : ∀ n, Mono (X.sigma n).right)
    (hOmega : X.OmegaCondition) : OmegaSpectrum.{u} where
  level := X.level
  sigma := X.sigma
  sigma_mono := hmono
  omega_condition := hOmega

end KanSequence

/-- 概要：Ω スペクトルの Kan 列への忘却。
方針：同じ段と構造射を使う。
規約：単射性と Ω 条件の証明だけを忘れる。
使われ方：BF 1978 §2。既存対象と置換前の列との共通界面。 -/
def OmegaSpectrum.toKanSequence (X : OmegaSpectrum.{u}) : KanSequence.{u} where
  level := X.level
  sigma := X.sigma

/-- 概要：Ω スペクトルから忘却した列は Ω 条件を満たす。
方針：対象に含まれる証明を使う。
規約：全基点の π_* 同型の条件。
使われ方：BF 1978 §2、HA §1.4.2。置換の入力。 -/
theorem OmegaSpectrum.toKanSequence_omega (X : OmegaSpectrum.{u}) :
    X.toKanSequence.OmegaCondition := X.omega_condition

end SerrePositivity.KST.Spectra
