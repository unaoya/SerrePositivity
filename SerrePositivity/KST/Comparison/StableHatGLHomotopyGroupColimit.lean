module

public import SerrePositivity.KST.Comparison.StableHatGLHomotopyColimit
public import SerrePositivity.KST.Comparison.CoefficientMatrixStabilization
public import SerrePositivity.KST.Spectra.FilteredHomotopyGroups

/-!
# 安定 ĜL の正次数の群の余極限

概要：有限 rank の正次数の群の cocone は、安定 ĜL の実際の群を余極限とする。
方針：K-L9 の台集合の余極限の普遍性を、群の忘却の filtered colimit 保存と同型反映で持ち上げる。
規約：KST Lemma 2.13 の安定 rank の高次の群。群演算を輸送で定義し直さない。
使われ方：有限 rank の係数群の自然同型の余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits SSet

/--
概要：有限 rank の点付き ĜL に正次数の群を施した図式。
方針：各射には K-L9 の点付き誘導準同型を使う。
規約：添字圏の宇宙を AsSmall で揃えている。
使われ方：安定対象の正次数の群の余極限。
-/
abbrev stableHatGLHomotopyGroupDiagram (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    AsSmall.{u} ℕ ⥤ GrpCat.{u} :=
  Spectra.pointedHomotopyGroupDiagram (stableHatGLLiftedPointedDiagram A) n

/--
概要：有限 rank の群から安定 ĜL の群への cocone。
方針：実際の点付き cocone の各脚の誘導準同型を使う。
規約：安定対象の群演算は K-L9 の既存のもの。
使われ方：群としての余極限の普遍性。
-/
abbrev stableHatGLHomotopyGroupCocone (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    Cocone (stableHatGLHomotopyGroupDiagram A n) :=
  Spectra.pointedHomotopyGroupCocone (stableHatGLLiftedPointedCocone A) n

/--
概要：有限 rank の正次数の群の図式は余極限を持つ。
方針：Mathlib の実際の filtered colimit の cocone を使う。
規約：対象は群の圏、添字圏の宇宙は値宇宙と揃える。
使われ方：忘却関手での余極限の反映。
-/
instance stableHatGLHomotopyGroupDiagram_hasColimit (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    HasColimit (stableHatGLHomotopyGroupDiagram A n) :=
  HasColimit.mk ⟨GrpCat.FilteredColimits.colimitCocone _,
    GrpCat.FilteredColimits.colimitCoconeIsColimit _⟩

/--
概要：群の cocone の台集合は K-L9 の余極限の cocone である。
方針：正次数の群の台集合と共通のホモトピー類の定義を照合する。
規約：次数 n+1 の既証明の台集合の普遍性を用いる。
使われ方：群の忘却による普遍性の反映。
-/
def stableHatGLHomotopyGroupCocone_underlyingIsColimit
    (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    IsColimit ((forget GrpCat).mapCocone (stableHatGLHomotopyGroupCocone A n)) :=
  stableHatGLHomotopyIsColimit A (n + 1)

/--
概要：安定 ĜL の実際の正次数の群は有限 rank の群の余極限である。
方針：群の忘却の filtered colimit 保存と同型反映で台集合の普遍性を反映する。
規約：KST Lemma 2.13 の群としての rank の安定化。
使われ方：有限 rank の係数表示を安定化する。
-/
def stableHatGLHomotopyGroupIsColimit (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    IsColimit (stableHatGLHomotopyGroupCocone A n) :=
  Spectra.pointedHomotopyGroupIsColimit (stableHatGLLiftedPointedCocone A)
    (stableHatGLLiftedPointedCocone_underlyingIsColimit A) n

/--
概要：有限 rank の正次数の群の余極限と安定 ĜL の既存の群の同型。
方針：同じ図式の二つの実際の余極限の一意性を使う。
規約：群の同型として普遍性を公開する。
使われ方：安定係数行列群との同型への合成。
-/
def stableHatGLHomotopyGroupColimitIso (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    colimit (stableHatGLHomotopyGroupDiagram A n) ≅
      GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidSpace (stableHatGL A)) n
        (monoidPointed (stableHatGL A)).basepoint) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (stableHatGLHomotopyGroupIsColimit A n)

end SerrePositivity.KST.Comparison
