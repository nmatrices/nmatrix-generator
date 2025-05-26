Forest.vo Forest.glob Forest.v.beautified Forest.required_vo: Forest.v 
Forest.vio: Forest.v 
Forest.vos Forest.vok Forest.required_vos: Forest.v 
PowerSet.vo PowerSet.glob PowerSet.v.beautified PowerSet.required_vo: PowerSet.v 
PowerSet.vio: PowerSet.v 
PowerSet.vos PowerSet.vok PowerSet.required_vos: PowerSet.v 
rnk/rnk.vo rnk/rnk.glob rnk/rnk.v.beautified rnk/rnk.required_vo: rnk/rnk.v Forest.vo PowerSet.vo
rnk/rnk.vio: rnk/rnk.v Forest.vio PowerSet.vio
rnk/rnk.vos rnk/rnk.vok rnk/rnk.required_vos: rnk/rnk.v Forest.vos PowerSet.vos
rnk/Model.vo rnk/Model.glob rnk/Model.v.beautified rnk/Model.required_vo: rnk/Model.v Forest.vo rnk/rnk.vo
rnk/Model.vio: rnk/Model.v Forest.vio rnk/rnk.vio
rnk/Model.vos rnk/Model.vok rnk/Model.required_vos: rnk/Model.v Forest.vos rnk/rnk.vos
rnk/Language.vo rnk/Language.glob rnk/Language.v.beautified rnk/Language.required_vo: rnk/Language.v Forest.vo rnk/rnk.vo rnk/Model.vo
rnk/Language.vio: rnk/Language.v Forest.vio rnk/rnk.vio rnk/Model.vio
rnk/Language.vos rnk/Language.vok rnk/Language.required_vos: rnk/Language.v Forest.vos rnk/rnk.vos rnk/Model.vos
rnk/RelCond.vo rnk/RelCond.glob rnk/RelCond.v.beautified rnk/RelCond.required_vo: rnk/RelCond.v Forest.vo rnk/rnk.vo rnk/Language.vo
rnk/RelCond.vio: rnk/RelCond.v Forest.vio rnk/rnk.vio rnk/Language.vio
rnk/RelCond.vos rnk/RelCond.vok rnk/RelCond.required_vos: rnk/RelCond.v Forest.vos rnk/rnk.vos rnk/Language.vos
