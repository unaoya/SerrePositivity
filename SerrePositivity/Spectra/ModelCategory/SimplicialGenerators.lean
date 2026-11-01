module
public import SerrePositivity.InfinityCategories.ModelBridge.HA.Generators

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators

/-! # Compatibility names for the shared simplicial generating-map theory -/

@[expose] public section
namespace SerrePositivity.SimplicialModelInputs

alias boundaryGenerator_domain_presentable :=
  SerrePositivity.SimplicialModel.boundaryGenerator_domain_presentable
alias hornGenerator_domain_presentable :=
  SerrePositivity.SimplicialModel.hornGenerator_domain_presentable
alias boundaryGenerators_isSmall := SerrePositivity.SimplicialModel.boundaryGenerators_isSmall
alias boundaryGenerators_cardinal := SerrePositivity.SimplicialModel.boundaryGenerators_cardinal
alias boundaryGenerators_smallObjectArgument :=
  SerrePositivity.SimplicialModel.boundaryGenerators_smallObjectArgument
alias hornGenerators_smallObjectArgument :=
  SerrePositivity.SimplicialModel.hornGenerators_smallObjectArgument
alias boundaryGenerators_leftClass := SerrePositivity.SimplicialModel.boundaryGenerators_leftClass
alias simplicialSet_isCofibrant := SerrePositivity.SimplicialModel.simplicialSet_isCofibrant

end SerrePositivity.SimplicialModelInputs
