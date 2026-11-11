module

public import SerrePositivity.KST.Spectra.PointedSequence
public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.KST.Spectra.PointedExtension
public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：Kan でない点つき列の構造射を含む段ごとの Kan 置換。
方針：構造射の随伴を Kan な loop 標的へ移し、anodyne な置換単位に沿って延長する。
規約：得られるのは Kan 列。任意の入力から Ω 条件が従うとは主張しない。
使われ方：BF 1978 §2、HTT A.3.3。K 理論空間の段ごとの Kan 置換。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 列を Kan 条件を持たない点つき列へ忘れる。
方針：同じ段と構造射を使う。
規約：データは変えず Kan 性の証明だけを忘れる。
使われ方：BF 1978 §2。置換との比較の共通の列。 -/
def KanSequence.toPointedSequence (X : KanSequence.{u}) : PointedSequence.{u} where
  level n := (X.level n).space
  sigma := X.sigma

namespace PointedSequence

/-- 概要：次段を Kan 置換した構造射の随伴。
方針：元の構造射と次段の置換単位を合成して curry する。
規約：標的の loop は Kan。
使われ方：Goerss–Jardine I §7、BF 1978 §2。元の段からの延長データ。 -/
def adjointToKanNext (X : PointedSequence.{u}) (n : ℕ) :
    X.level n ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedKanReplacement.obj (X.level (n + 1))) :=
  MonoidalClosed.curry (X.sigma n ≫ PointedKanReplacement.unit.app (X.level (n + 1)))

/-- 概要：Kan 置換した段から次段の loop への延長された随伴構造射。
方針：anodyne な単位に沿って Kan な loop 標的へ点つき延長する。
規約：この延長の選択に関手性は主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。置換列の構造射の構成。 -/
def kanReplacementAdjoint (X : PointedSequence.{u}) (n : ℕ) :
    PointedKanReplacement.obj (X.level n) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedKanReplacement.obj (X.level (n + 1))) :=
  PointedExtension.extend
    (show X.level n ⟶ PointedKanReplacement.obj (X.level n) from
      PointedKanReplacement.unit.app (X.level n))
    (PointedKanReplacement.unit_anodyne (X.level n)) (adjointToKanNext X n)

/-- 概要：置換した二段の間の suspension 構造射。
方針：延長した随伴構造射を uncurry する。
規約：構造射の単射性と Ω 条件はここでは主張しない。
使われ方：BF 1978 §2、HTT A.3.3。段ごとの Kan 置換の列への接続。 -/
def kanReplacementSigma (X : PointedSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedKanReplacement.obj (X.level n)) ⟶
      PointedKanReplacement.obj (X.level (n + 1)) :=
  MonoidalClosed.uncurry (kanReplacementAdjoint X n)

/-- 概要：置換単位は suspension 構造射と厳密可換。
方針：uncurry の自然性、延長の制限式、curry の逆関係を使う。
規約：点つき射の等式。
使われ方：BF 1978 §2、HTT A.3.3。列全体の置換の比較射。 -/
theorem kanReplacement_unit_comm (X : PointedSequence.{u}) (n : ℕ) :
    PointedSimplicialSet.circle.{u} ◁ PointedKanReplacement.unit.app (X.level n) ≫
        kanReplacementSigma X n = X.sigma n ≫ PointedKanReplacement.unit.app (X.level (n + 1)) := by
  have h := PointedExtension.comp_extend
    (Z := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedKanReplacement.obj (X.level (n + 1))))
    (show X.level n ⟶ PointedKanReplacement.obj (X.level n) from
      PointedKanReplacement.unit.app (X.level n))
    (PointedKanReplacement.unit_anodyne (X.level n)) (adjointToKanNext X n)
  unfold kanReplacementSigma
  rw [← MonoidalClosed.uncurry_natural_left]
  exact (congrArg (fun t : X.level n ⟶
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedKanReplacement.obj (X.level (n + 1))) ↦ MonoidalClosed.uncurry t) h).trans
      (MonoidalClosed.uncurry_curry _)

/-- 概要：任意の点つき列を、構造射を備えた Kan 列へ置換する。
方針：既存の Kan 置換の各段と、延長した suspension 構造射を束ねる。
規約：一般の入力について Ω スペクトル化を主張しない。
使われ方：BF 1978 §2、HTT A.3.3。Kan でない列の実際の置換。 -/
def kanReplacement (X : PointedSequence.{u}) : KanSequence.{u} where
  level n := {
    space := PointedKanReplacement.obj (X.level n)
    kan := PointedKanReplacement.obj_kanComplex (X.level n) }
  sigma := kanReplacementSigma X

/-- 概要：元の点つき列から置換した列への厳密な比較射。
方針：各段の単位と構造射との厳密可換式を使う。
規約：Kan 条件を忘れた列の射。
使われ方：BF 1978 §2、HTT A.3.3。K 理論空間の列の比較。 -/
def kanReplacementUnit (X : PointedSequence.{u}) : Hom X X.kanReplacement.toPointedSequence where
  app n := PointedKanReplacement.unit.app (X.level n)
  comm := kanReplacement_unit_comm X

/-- 概要：元の指定段が Kan なら、列の置換単位はその段で全基点 π_* 同型。
方針：点つき Kan 置換の anodyne 単位に対する検証済みの定理を使う。
規約：元の段の Kan 性を明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Kan な列の段ごとの保存。 -/
theorem kanReplacementUnit_piIsomorphism (X : PointedSequence.{u}) (n : ℕ)
    [KanComplex (X.level n).right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (X.level n).right) (Y := (X.kanReplacement.level n).space.right)
      (X.kanReplacementUnit.app n).right :=
  PointedKanReplacement.unit_piIsomorphism (X.level n)

end PointedSequence

end

end SerrePositivity.KST.Spectra
