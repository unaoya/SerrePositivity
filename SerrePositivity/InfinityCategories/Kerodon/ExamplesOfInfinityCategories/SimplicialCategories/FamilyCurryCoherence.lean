module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StraighteningFamilyCounit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：図式の族の同型の currying と合成・制限の整合性。
方針：内部 currying の前合成との可換式を頂点同型へ写す。
規約：端点の curry の自然性による等式を明示する。
使われ方：余単位の底変換の自然性を任意の族へ移す。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：内部 currying は第二因子の前合成と可換。
方針：二重の関手空間の各成分でパラメーター射の自然性を使う。
規約：単体集合の射の厳密な等式。
使われ方：族の同型の currying と制限を結ぶ。 -/
lemma coherentFamilyCurryMap_pre (A X : SSet.{u}) {K L : SSet.{u}} (i : L ⟶ K) :
    (pre (A ◁ i)).app X ≫ (ihomCurryIso A L X).hom =
      (ihomCurryIso A K X).hom ≫ (pre i).app ((ihom A).obj X) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro l
  apply CategoryTheory.Functor.functorHom_ext
  intro d β
  apply ConcreteCategory.hom_ext
  intro a
  change F.app d (α ≫ β) (a, i.app d (L.map β l)) =
    F.app d (α ≫ β) (a, K.map β (i.app m l))
  exact congrArg (fun z : K.obj d ↦ F.app d (α ≫ β) (a, z))
    (ConcreteCategory.congr_hom (i.naturality β) l)

/-- 概要：族の同型の currying は合成を保つ。
方針：頂点同型の像の合成則を使う。
規約：同型を新たに選ばない。
使われ方：余単位の自然性の可換式を curry する。 -/
lemma coherentFamilyCurryIso_trans {A B X : SSet.{u}} {f g h : A ⊗ B ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso (e ≪≫ d) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso e ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans e d (ihomCurryIso A B X).hom

/-- 概要：図式の等式による同型は curry した図式の等式の同型へ写る。
方針：等式を消去して恒等同型の像を計算する。
規約：端点の移送を保持する。
使われ方：curry の自然性による終点の同定。 -/
lemma coherentFamilyCurryIso_eqToIso {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X} (h : f = g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso
      (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)) h)) =
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry d))) h) := by
  subst g
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map, Functor.mapIso_refl, eqToIso_refl]
  rfl

/-- 概要：族の同型の currying はパラメーターでの前合成を保つ。
方針：内部 currying の可換式を同型の像へ移す。
規約：curry の自然性による始点と終点の移送を明示する。
使われ方：任意の族への余単位の制限。 -/
lemma coherentFamilyCurryIso_precomp {A K L X : SSet.{u}} {f g : A ⊗ K ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (i : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso (e.precomp (A ◁ i)) =
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
        (curry_natural_left i f)) ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso e).precomp i ≪≫
      (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
        (curry_natural_left i g))).symm := by
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_congr e
    ((pre (A ◁ i)).app X ≫ (ihomCurryIso A L X).hom)
    ((ihomCurryIso A K X).hom ≫ (pre i).app ((ihom A).obj X))
    (coherentFamilyCurryMap_pre A X i)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e ((pre (A ◁ i)).app X)) (ihomCurryIso A L X).hom =
    eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
      (curry_natural_left i f)) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (ihomCurryIso A K X).hom)
      ((pre i).app ((ihom A).obj X)) ≪≫
    (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
      (curry_natural_left i g))).symm
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp]
  rw [ha]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
