"use strict;"


function box(t, v) {
    return {tag: t, value: v};
}

function getTypeTag(b) {
    return b.tag;
}

function unbox(b) {
    return b.value;
}

export {
    box, getTypeTag, unbox
};
