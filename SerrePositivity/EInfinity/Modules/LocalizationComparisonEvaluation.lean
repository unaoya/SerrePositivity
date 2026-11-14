module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorHoEvaluation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoTriangleEvaluation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
# 同じ局所化比較の前合成と頂点評価

概要：HTT §1.2.7 の全関手間の比較の成分は、元の頂点の像で評価される。
方針：同じ二胞体の辺代表に戻して、定値単体の自然性を使う。
規約：比較の選択を変えない。
使われ方：M10 の円筒の全比較と指定された弱辺の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open scoped Simplicial

/-- 概要：同じ二胞体の前合成の評価は像の頂点での評価（HTT §1.2.7）。
方針：同じ辺代表を取り、定値一単体を元の写像で移す。
規約：同じホモトピー圏の射。使われ方：可逆比較の成分の前合成則。 -/
lemma functorHomotopyEvaluation_precomp_map_app {A B Y : SSet.{u}} [Quasicategory Y]
    (q : A ⟶ B) {v w : ((ihom B).obj Y) _⦋0⦌}
    (a : (SSet.HomotopyCategory.mk v : hoFunctor.obj ((ihom B).obj Y)) ⟶
      SSet.HomotopyCategory.mk w) (x : A _⦋0⦌) :
    ((functorHomotopyEvaluation A Y).map
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map a)).app (SSet.HomotopyCategory.mk x) =
      ((functorHomotopyEvaluation B Y).map a).app
        (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) x)) := by
  obtain ⟨e, rfl⟩ := IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective v w a
  change SSet.Truncated.HomotopyCategory.homMk _ =
    SSet.Truncated.HomotopyCategory.homMk _
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  change e.edge.app (Opposite.op ⦋1⦌) (𝟙 _)
      (q.app (Opposite.op ⦋1⦌) (A.σ 0 x)) =
    e.edge.app (Opposite.op ⦋1⦌) (𝟙 _)
      (B.σ 0 (q.app (Opposite.op ⦋0⦌) x))
  congr 1
  exact ConcreteCategory.congr_hom (q.naturality (SimplexCategory.σ (n := 0) 0).op) x

/-- 概要：同じ可逆な全比較の前合成は成分を保つ（HTT §1.2.7）。
方針：元の自然同型への端点輸送を消し、同じ射の評価の前合成則を使う。
規約：元の比較そのもの。使われ方：円筒比較の両端点の成分の回収。 -/
lemma functorIso_precomp_hom_app {A B Y : SSet.{u}} [Quasicategory Y]
    {f g : B ⟶ Y} (e : FunctorIso f g) (q : A ⟶ B) (x : A _⦋0⦌) :
    (e.precomp q).toNatIso.hom.app (SSet.HomotopyCategory.mk x) =
      e.toNatIso.hom.app (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) x)) := by
  simp only [FunctorIso.toNatIso, FunctorIso.precomp, VertexIso.map, Iso.trans_hom,
    Iso.symm_hom, eqToIso.hom, eqToIso.inv, NatTrans.comp_app, eqToHom_app,
    eqToHom_refl, Category.id_comp, Category.comp_id, Functor.mapIso_hom]
  exact functorHomotopyEvaluation_precomp_map_app q e.hom x

/-- 概要：全関手の等式の比較は同じ頂点の等式に評価される（HTT §1.2.7）。
方針：同じ関手の等式を消去する。
規約：等式の証明を選び直しても成分は同じ。使われ方：円筒比較の端点の回収。 -/
lemma functorIso_eqToIso_hom_app {A Y : SSet.{u}} {f g : A ⟶ Y}
    (h : f = g) (x : A _⦋0⦌) :
    (show FunctorIso f g from
      eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) h)).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x) =
    eqToHom (congrArg (fun k : A ⟶ Y => SSet.HomotopyCategory.mk
      (k.app (Opposite.op ⦋0⦌) x)) h) := by
  subst g
  simp [FunctorIso.toNatIso]

attribute [cite HTT "1.2.7" (partial := component)
  "元の全関手比較の前合成と成分評価の法則だけを照合する。局所化の普遍性は含まない。"]
  functorHomotopyEvaluation_precomp_map_app functorIso_precomp_hom_app
  functorIso_eqToIso_hom_app

end SerrePositivity.EInfinity.Modules
