module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom

/-!
概要：関手同型の前後合成による同型の合成と逆の保存。
方針：内部 Hom の射が誘導するホモトピー圏の関手を使う。
規約：元の指定同型に作用する。
使われ方：比較円柱の内部同型の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：関手同型の前後合成はホモトピー圏の同型の関手性を保つ。
方針：誘導された関手の mapIso の式へ戻す。
規約：合成と逆同型の値を保持する。
使われ方：円柱の三つの関係を脚の比較同型の式へまとめる。 -/
lemma functorIso_precomp_eq_mapIso {W X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : W ⟶ X) :
    e.precomp q = (SSet.mapHomotopyCategory ((pre q).app Y)).mapIso e := by
  apply Iso.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom e q
/-- 概要：関手同型の前後合成はホモトピー圏の同型の関手性を保つ。
方針：誘導された関手の mapIso の式へ戻す。
規約：合成と逆同型の値を保持する。
使われ方：円柱の三つの関係を脚の比較同型の式へまとめる。 -/
lemma functorIso_postcomp_eq_mapIso {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : Y ⟶ Z) :
    e.postcomp q = (SSet.mapHomotopyCategory ((ihom X).map q)).mapIso e := by
  apply Iso.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom e q
/-- 概要：関手同型の前後合成はホモトピー圏の同型の関手性を保つ。
方針：誘導された関手の mapIso の式へ戻す。
規約：合成と逆同型の値を保持する。
使われ方：円柱の三つの関係を脚の比較同型の式へまとめる。 -/
lemma functorIso_precomp_trans {W X Y : SSet.{u}} {f g h : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) (q : W ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (e ≪≫ d) q = e.precomp q ≪≫ d.precomp q := by
  simp only [functorIso_precomp_eq_mapIso, Functor.mapIso_trans]
/-- 概要：関手同型の前後合成はホモトピー圏の同型の関手性を保つ。
方針：誘導された関手の mapIso の式へ戻す。
規約：合成と逆同型の値を保持する。
使われ方：円柱の三つの関係を脚の比較同型の式へまとめる。 -/
lemma functorIso_postcomp_trans {X Y Z : SSet.{u}} {f g h : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) (q : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (e ≪≫ d) q = e.postcomp q ≪≫ d.postcomp q := by
  simp only [functorIso_postcomp_eq_mapIso, Functor.mapIso_trans]
/-- 概要：関手同型の前後合成はホモトピー圏の同型の関手性を保つ。
方針：誘導された関手の mapIso の式へ戻す。
規約：合成と逆同型の値を保持する。
使われ方：円柱の三つの関係を脚の比較同型の式へまとめる。 -/
lemma functorIso_precomp_symm {W X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : W ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm q = (e.precomp q).symm := by
  simp only [functorIso_precomp_eq_mapIso, Functor.mapIso_symm]
/-- 概要：関手同型の前後合成はホモトピー圏の同型の関手性を保つ。
方針：誘導された関手の mapIso の式へ戻す。
規約：合成と逆同型の値を保持する。
使われ方：円柱の三つの関係を脚の比較同型の式へまとめる。 -/
lemma functorIso_postcomp_symm {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.symm q = (e.postcomp q).symm := by
  simp only [functorIso_postcomp_eq_mapIso, Functor.mapIso_symm]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
