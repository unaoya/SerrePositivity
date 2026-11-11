module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplexFibers

/-!
概要：小さい次数 fiber の恒等射・合成・合成からの反映・左積での保存。
方針：fiber を小さい直和や元の fiber への単射で符号化する。
規約：底と全空間自体の小ささは仮定しない。
使われ方：相対射の collage の次数 fiber の小ささ。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：恒等射の次数 fiber は小さい。
方針：指定単体の逆像が高々一点であることを使う。
規約：元の単体集合は大きくてもよい。
使われ方：relative join の右因子の恒等射。 -/
lemma hasSmallSimplexFibers_id (E : SSet.{u + 1}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers (𝟙 E) := by
  intro n b
  have : Subsingleton {x : E.obj n // (𝟙 E : E ⟶ E).app n x = b} := ⟨by
    intro x y
    exact Subtype.ext (x.property.trans y.property.symm)⟩
  infer_instance

/-- 概要：小さい次数 fiber の条件は合成で保存される。
方針：合成の fiber を二段の fiber の小さい直和へ単射で入れる。
規約：中間の全空間の小ささは不要。
使われ方：collage から区間付きの底への射影。 -/
lemma HasSmallSimplexFibers.comp {E F B : SSet.{u + 1}}
    {p : E ⟶ F} {q : F ⟶ B} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers (p ≫ q) := by
  intro n b
  have : Small.{u} {y : F.obj n // q.app n y = b} := hq n b
  have (y : {y : F.obj n // q.app n y = b}) :
      Small.{u} {x : E.obj n // p.app n x = y.val} := hp n y.val
  let T := Σ y : {y : F.obj n // q.app n y = b}, {x : E.obj n // p.app n x = y.val}
  let code : {x : E.obj n // (p ≫ q).app n x = b} → T := fun x ↦
    ⟨⟨p.app n x.val, x.property⟩, x.val, rfl⟩
  apply small_of_injective (f := code)
  intro x y h
  exact Subtype.ext (congrArg (fun t : T ↦ t.2.val) h)

/-- 概要：合成の次数 fiber が小さければ最初の射の次数 fiber も小さい。
方針：終点を固定した fiber を合成の指定単体の fiber へ単射で入れる。
規約：後の射に条件は不要。
使われ方：底上の相対射自体の小ささを元の始域の射影から得る。 -/
lemma HasSmallSimplexFibers.of_comp_right {E F B : SSet.{u + 1}}
    (p : E ⟶ F) (q : F ⟶ B) (hpq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers (p ≫ q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p := by
  intro n b
  have := hpq n (q.app n b)
  let code : {x : E.obj n // p.app n x = b} →
      {x : E.obj n // (p ≫ q).app n x = q.app n b} :=
    fun x ↦ ⟨x.val, congrArg (fun y ↦ q.app n y) x.property⟩
  exact small_of_injective (f := code) (by
    intro x y h
    exact Subtype.ext (congrArg
      (fun z : {x : E.obj n // (p ≫ q).app n x = q.app n b} ↦ z.val) h))

/-- 概要：任意の単体集合を左因子とする積は次数 fiber の小ささを保つ。
方針：第二射影の cartesian 正方形へ元の条件を移す。
規約：左因子の小ささは不要。
使われ方：区間と元の射影の積。 -/
lemma HasSmallSimplexFibers.tensor_left {E B : SSet.{u + 1}} {p : E ⟶ B}
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (K : SSet.{u + 1}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers (K ◁ p) := by
  apply hp.of_isPullback (e := snd K E) (g := snd K B)
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    have hk : (x.1, p.app n x.2) = (y.1, p.app n y.2) := h.2
    exact Prod.ext (congrArg (fun z : K.obj n × B.obj n ↦ z.1) hk) h.1
  · intro x y h
    exact ⟨(y.1, x), rfl, Prod.ext rfl h⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
