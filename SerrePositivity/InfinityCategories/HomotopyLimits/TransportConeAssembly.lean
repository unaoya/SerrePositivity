module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeLeftFibration
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffold

/-!
概要：strict transport の互換な族を元の射影上の切断の族へ組み立てる。
方針：通常の錐から simplicial replacement へ写し、universal scaffold で評価する。
規約：この構成自体には left fibration 性を要求しない。
使われ方：Kerodon 5.3.4.7、7.4.1.6、7.5.4.6 の切断と strict transport の極限の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：図式の通常の錐は底の nerve と錐頂点から simplicial replacement への射を与える。
方針：各底の射列に始点での錐の成分を添え、始点が動く自然性に錐の可換性を使う。
規約：係数は元の錐の頂点の単体から作る。
使われ方：Kerodon 5.3.2.1、5.3.4.7 の互換な族の対角への組み立て。 -/
noncomputable def coneReplacementMap {H : I ⥤ SSet.{u}} (c : Cone H) :
    nerve I ⊗ c.pt ⟶ simplicialReplacement H where
  app d := ↾fun s => ⟨s.1, SSet.yonedaEquiv.symm s.2 ≫ c.π.app (s.1.obj 0)⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, a⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change SSet.yonedaEquiv.symm (c.pt.map α a) ≫ c.π.app (σ.obj (α.unop.toOrderHom 0)) =
      stdSimplex.map α.unop ≫ (SSet.yonedaEquiv.symm a ≫ c.π.app (σ.obj 0)) ≫
        H.map (σ.map (homOfLE (Fin.zero_le _)))
    have hy : SSet.yonedaEquiv.symm (c.pt.map α a) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm a :=
      (SSet.yonedaEquiv_symm_naturality_left (X := c.pt) α.unop a).symm
    rw [hy]
    simp only [Category.assoc]
    rw [c.w]

/-- 概要：錐から simplicial replacement への射は底で第一射影である。
方針：各単体で元の底の射列を使うことを計算する。
規約：底への一致は厳密な等式。
使われ方：Kerodon 5.3.4.7、7.4.1.6 の組み立ての底の固定条件。 -/
lemma coneReplacementMap_projection {H : I ⥤ SSet.{u}} (c : Cone H) :
    coneReplacementMap c ≫ simplicialReplacementProjection H = fst (nerve I) c.pt := rfl

/-- 概要：strict transport 図式の互換な族を元の全空間への切断の族に組み立てる。
方針：simplicial replacement を経由し、既存の universal scaffold で評価する。
規約：元の全空間への実際の射を作る。
使われ方：Kerodon 5.3.4.7、7.4.1.6、7.5.4.6 の strict transport の切断への復元。 -/
noncomputable def strictTransportConeAssembly {E : SSet.{u}} (p : E ⟶ nerve I)
    (c : Cone (leftStrictTransportDiagram p)) : nerve I ⊗ c.pt ⟶ E :=
  coneReplacementMap c ≫ universalScaffold p

/-- 概要：strict transport の族の組み立ては元の底の上の切断の族である。
方針：universal scaffold と simplicial replacement の底への射影の式を使う。
規約：p の充填性は不要。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断空間への持ち上げ条件。 -/
lemma strictTransportConeAssembly_projection {E : SSet.{u}} (p : E ⟶ nerve I)
    (c : Cone (leftStrictTransportDiagram p)) :
    strictTransportConeAssembly p c ≫ p = fst (nerve I) c.pt := by
  rw [strictTransportConeAssembly, Category.assoc, universalScaffold_projection,
    coneReplacementMap_projection]

/-- 概要：strict transport 図式の通常の錐は元の射影の切断空間への射を与える。
方針：組み立てた切断の族を切断空間へ持ち上げる。
規約：錐が極限錐であることは定義に要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の strict transport の極限から切断模型への比較。 -/
noncomputable def strictTransportConeSections {E : SSet.{u}} (p : E ⟶ nerve I)
    (c : Cone (leftStrictTransportDiagram p)) : c.pt ⟶ simplicialSections p :=
  simplicialSectionsLift (strictTransportConeAssembly p c)
    (strictTransportConeAssembly_projection p c)

end SerrePositivity.InfinityCategories.HomotopyLimits
