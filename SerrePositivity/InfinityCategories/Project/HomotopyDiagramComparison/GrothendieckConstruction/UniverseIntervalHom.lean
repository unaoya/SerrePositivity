module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniverseInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PointEndpointEvaluation

/-!
概要：区間の関手空間と ULift の標準同型、および端点評価の厳密な整合性。
方針：内部 Hom の比較と標準単体の宇宙の同型を合成し、各次数の評価を計算する。
規約：端点の番号は保持する。Kan 性は不要。
使われ方：HTT 4.2.4.1、可逆 path と導来 fiber の宇宙の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：内部 Hom の ULift の標準比較は固定頂点での評価と厳密に可換。
方針：全次数で元の関手の頂点の定値単体での評価を計算する。
規約：指定頂点も ULift.up で持ち上げる。
使われ方：区間の両端点と導来 fiber の固定条件の保持。 -/
lemma uliftInternalHomComparison_evaluate (K B : SSet.{u}) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison.{u, v} K B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y :=
        (SSet.uliftFunctor.{v, u}).obj B) (ULift.up k) =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) k) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  rfl

/-- 概要：小さい宇宙の区間関手空間の ULift と大きい宇宙の区間関手空間の同型。
方針：内部 Hom の標準同型の後で、始域を標準区間の宇宙の同型で前合成する。
規約：大きい宇宙の区間は標準の Δ[1] そのもの。
使われ方：可逆 path の包含の標準同型との合成。 -/
def uliftIntervalHomIso (B : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom (Δ[1] : SSet.{u})).obj B) ≅
      (ihom (Δ[1] : SSet.{max u v})).obj ((SSet.uliftFunctor.{v, u}).obj B) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomIso Δ[1] B ≪≫
    (internalHom.mapIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).symm.op).app
      ((SSet.uliftFunctor.{v, u}).obj B)

/-- 概要：区間関手の ULift の同型は両端点評価と厳密に可換。
方針：前合成した関手の評価を頂点の像へ移し、内部 Hom の評価の比較を使う。
規約：端点 j は元の区間と同じ番号を使う。
使われ方：導来 fiber の path の始点・終点の固定条件の移送。 -/
lemma uliftIntervalHomIso_hom_evaluate (B : SSet.{u}) (j : Fin 2) :
    (uliftIntervalHomIso.{u, v} B).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (SSet.uliftFunctor.{v, u}).obj B) (stdSimplex.obj₀Equiv.symm j) =
      (SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm j)) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison Δ[1] B ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).inv).app ((SSet.uliftFunctor.{v, u}).obj B)) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  exact uliftInternalHomComparison_evaluate _ _ _

/-- 概要：区間関手の ULift の標準同型は標的への後合成と厳密に可換。
方針：各次数で元の関手の値に元の標的の射を適用する。
規約：射 p と両端の単体集合は任意。
使われ方：可逆 path の写像と path 置換の全空間の比較。 -/
lemma uliftIntervalHomIso_hom_naturality {E B : SSet.{u}} (p : E ⟶ B) :
    (uliftIntervalHomIso.{u, v} E).hom ≫
        (ihom (Δ[1] : SSet.{max u v})).map ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map ((ihom (Δ[1] : SSet.{u})).map p) ≫
        (uliftIntervalHomIso.{u, v} B).hom := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
